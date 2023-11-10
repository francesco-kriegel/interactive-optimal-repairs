package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.CompatibilityMode.*
import interactive_optimal_repairs.IQSaturation.toShortDLString
import interactive_optimal_repairs.QueryLanguage.*
import interactive_optimal_repairs.Util.{ImplicitIterableOfOWLClassExpressions, ImplicitOWLClassExpression, ImplicitOWLIndividual, ImplicitOWLObjectPropertyExpression, Nominal}
import protege_components.Util.htmlParagraph

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*

import scala.collection.mutable

enum CompatibilityMode(val description: String) {
  case NO extends CompatibilityMode("Use anonymous individuals (default mode)")
  case FRESH_NAMED_INDIVIDUALS extends CompatibilityMode("Use fresh named individuals (compatibility mode)")
  case EXPLICIT_NAMED_INDIVIDUALS extends CompatibilityMode(htmlParagraph("Use named individuals that indicate the pair in the formal construction (inspection mode, do not use in production)"))
}

object Repair {

  def apply(queryLanguage: QueryLanguage, seed: RepairSeed)(using configuration: RepairConfiguration)(using ontologyManager: OWLOntologyManager): Repair = {
    queryLanguage match
      case IQ => IQRepair(seed)
      case IRQ => IRQRepair(seed)
      case CQ => CQRepair(seed)
  }

}

trait Repair(val seed: RepairSeed)(using configuration: RepairConfiguration) {

  def entails(query: Query): Boolean = {
    val saturation = IQSaturation()
    query match
      case classAssertion @ ClassAssertion(_, classExpression, individual @ NamedIndividual(_)) if ELExpressivityChecker.checkClassExpression(classExpression) =>
        (configuration.ontologyReasoner entails classAssertion)
          && !(classExpression isCoveredBy seed(individual) wrt configuration.ontologyReasoner)
      case roleAssertion @ ObjectPropertyAssertion(_, property @ ObjectProperty(_), subject @ NamedIndividual(_), target @ NamedIndividual(_)) =>
        (configuration.axioms contains roleAssertion)
          && !(configuration.repairRequest.axioms contains roleAssertion)
          && (saturation.Succ(seed(subject), property, target) isCoveredBy seed(target) wrt configuration.trivialReasoner)
      case _ => ???
  }

  def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology

}

type IQSaturationNode = OWLIndividual | OWLClassExpression

object IQSaturation {

  def toShortDLString(node: IQSaturationNode): String = {
    node match
      case individual: OWLIndividual => individual.toShortDLString
      case classExpression: OWLClassExpression => classExpression.toShortDLString
  }

}

class IQSaturation(using configuration: RepairConfiguration) {

  val tboxSuccessors = mutable.HashMap[OWLClassExpression, mutable.HashSet[(OWLObjectProperty, OWLClassExpression)]]()
  configuration.axioms.foreach {
    case SubClassOf(_, subClass, superClass) =>
      tboxSuccessors.getOrElseUpdate(subClass, {
        mutable.HashSet[(OWLObjectProperty, OWLClassExpression)]()
      }) ++= superClass.topLevelConjuncts().collect { case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, filler) }
    case _ => // Do nothing.
  }

  def getSuccessorsInSaturation(node: IQSaturationNode): Iterable[(OWLObjectProperty, IQSaturationNode)] = {
    node match
      case individual: OWLIndividual =>
        configuration.axioms.collect[(OWLObjectProperty, IQSaturationNode)] {
          case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, target) if subject equals individual => (property, target)
        } ++ configuration.ontologyReasoner.premisesAmongTypes(individual).flatMap(tboxSuccessors)
      case classExpression: OWLClassExpression =>
        classExpression.topLevelConjuncts().collect[(OWLObjectProperty, IQSaturationNode)] {
          case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, filler)
        } ++ configuration.ontologyReasoner.premisesAmongSubsumers(classExpression).flatMap(tboxSuccessors)
  }

  def getLabelsInSaturation(node: IQSaturationNode): Iterable[OWLClass] = {
    node match
      case individual: OWLIndividual =>
        configuration.ontologyReasoner.types(individual).collect { case c@Class(_) => c }
      case classExpression: OWLClassExpression =>
        configuration.ontologyReasoner.subsumers(classExpression).collect { case c@Class(_) => c }
  }

  extension (node: IQSaturationNode) {
    infix def hasType(classExpression: OWLClassExpression): Boolean = {
      node match
        case individualNode: OWLIndividual => configuration.ontologyReasoner.types(individualNode) contains classExpression
        case classExpressionNode: OWLClassExpression => configuration.ontologyReasoner.subsumers(classExpressionNode) contains classExpression
    }
  }

  def Succ(repairType: RepairType, property: OWLObjectProperty, target: IQSaturationNode): collection.Set[OWLClassExpression] = {
    val succ = repairType.atoms.collect {
//      case ObjectSomeValuesFrom(qroperty, nominal@Nominal(uarget)) => if (property equals qroperty) && (target equals uarget) then nominal
//      case ObjectSomeValuesFrom(qroperty, filler) => if (property equals qroperty) && (target hasType filler) then filler
//      case ObjectHasValue(qroperty, uarget@NamedIndividual(_)) => if (property equals qroperty) && (target equals uarget) then Nominal(uarget)
      case ObjectSomeValuesFrom(qroperty, filler) if (property equals qroperty) && (target hasType filler) => filler
    }
    val types =
      target match
        case individual: OWLIndividual => Set.from(configuration.ontologyReasoner.types(individual))
        case classExpression: OWLClassExpression => Set.from(configuration.ontologyReasoner.subsumers(classExpression))
    if !(succ subsetOf types) then
      Console.err.println("Repair type: " + repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}"))
      Console.err.println("Property: " + property.toShortDLString)
      Console.err.println("Target node: " + toShortDLString(target))
      Console.err.println("Computed Succ: " + succ.map(_.toShortDLString).mkString("{", ",", "}"))
      Console.err.println("Types: " + types.map(_.toShortDLString).mkString("{", ",", "}"))
      throw RuntimeException() // sanity check, could be removed
    succ
  }

  lazy val isAcyclic: Boolean = {

    var isAcyclic = true

    var i = 0
    val index = mutable.HashMap[IQSaturationNode, Int]()
    val lowlink = mutable.HashMap[IQSaturationNode, Int]()
    val stack = mutable.Stack[IQSaturationNode]()
    val isOnStack = mutable.HashSet[IQSaturationNode]()
    val remainingNodes = mutable.HashSet[IQSaturationNode]()

    configuration.axioms.foreach {
      case ClassAssertion(_, _, individual) =>
        remainingNodes += individual
      case ObjectPropertyAssertion(_, _, subject, target) =>
        remainingNodes += subject
        remainingNodes += target
      case _ =>
        // Do nothing.
    }

    val whileLoop = new scala.util.control.Breaks
    whileLoop.tryBreakable {
      while (remainingNodes.nonEmpty) {
        val v = remainingNodes.head
        val cycleDetected = tarjan(v)
        if (cycleDetected)
          whileLoop.break()
      }
    } catchBreak {
      isAcyclic = false
    }

    def tarjan(v: IQSaturationNode): Boolean = {
      index(v) = i
      lowlink(v) = i
      i += 1
      stack.push(v)
      isOnStack(v) = true
      remainingNodes.remove(v)

      val forLoop = new scala.util.control.Breaks
      forLoop.tryBreakable {
        for (w <- getSuccessorsInSaturation(v).map(_._2)) {
          if (remainingNodes contains w)
            val cycleDetected = tarjan(w)
            if (cycleDetected)
              forLoop.break()
            else
              lowlink(v) = lowlink(v) min lowlink(w)
          else if (isOnStack(w))
            lowlink(v) = lowlink(v) min index(w)
        }
        if (lowlink(v) equals index(v)) {
          val scc = mutable.HashSet[IQSaturationNode]()
          while {
            val w = stack.pop()
            isOnStack(w) = false
            scc.add(w)
            !(w equals v)
          } do ()
          scc.size > 1
        } else {
          false
        }
      } catchBreak {
        true
      }
    }

    isAcyclic
  }

}

class IQRepair(repairSeed: RepairSeed)(using configuration: RepairConfiguration)(using ontologyManager: OWLOntologyManager) extends Repair(repairSeed) {

  override def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology = {
    val saturation = IQSaturation()
    val repair = ontologyManager.createOntology()
    val factory = CopiedOWLIndividual.FactoryIQ(compatibilityMode)
    val queue = mutable.Queue[CopiedOWLIndividual]()
    configuration.axioms foreach {
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        if saturation.Succ(repairSeed(subject), property, target) isCoveredBy repairSeed(target) wrt configuration.trivialReasoner then
          ontologyManager.addAxiom(repair, subject Fact (property, target))
      case _ => // Do nothing.
    }
    configuration.ontologyReasoner.instances(OWLThing).distinct
      .map(individual => factory.getCopyOrElseCreateCopyWithNamedIndividual(individual, repairSeed.getRepairType(individual)))
      .foreach(queue.enqueue)
    while queue.nonEmpty do
      val subject = queue.dequeue()
      saturation.getLabelsInSaturation(subject.individualInTheSaturation)
        .filterNot(subject.repairType.atoms.contains)
        .map(subject.individualInTheRepair Type _)
        .foreach(ontologyManager.addAxiom(repair, _))
      saturation.getSuccessorsInSaturation(subject.individualInTheSaturation)
        .foreach { (property, targetInTheSaturation) =>
          RepairTypes.computeAllMinimalRepairTypes(targetInTheSaturation, saturation.Succ(subject.repairType, property, targetInTheSaturation))
            .foreach { repairType =>
              val targetAlreadyExists = factory.containsCopy(targetInTheSaturation, repairType)
              val target = factory.getCopyOrElseCreateCopyWithAnonymousIndividual(targetInTheSaturation, repairType)
              ontologyManager.addAxiom(repair, subject.individualInTheRepair Fact (property, target.individualInTheRepair))
              if !targetAlreadyExists then queue.enqueue(target)
            }
        }
    repair
  }
}

class IRQRepair(repairSeed: RepairSeed)(using configuration: RepairConfiguration)(using ontologyManager: OWLOntologyManager)
  extends IQRepair({
    val newAxioms = mutable.HashSet.from[OWLClassAssertionAxiom](repairSeed.axioms)
    configuration.repairRequest.axioms foreach {
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        // newAxioms += (subject Type (property some Nominal(target))) // standard translation of role assertions into class assertions, as used in the KR 2022 paper
         val nominal = Nominal(target)
         val successor = property some nominal
         newAxioms += (subject Type successor) // standard translation of role assertions into class assertions, as used in the KR 2022 paper
         configuration.trivialReasoner.addRepresentative(nominal)
         configuration.trivialReasoner.addRepresentative(successor)
         configuration.ontologyReasoner.addRepresentative(nominal)
         configuration.ontologyReasoner.addRepresentative(successor)
      case _ => // Do nothing.
    }
    RepairSeed(repairSeed.preprocessed, newAxioms)
  }) {}

class CQRepair(repairSeed: RepairSeed)(using configuration: RepairConfiguration) extends Repair(repairSeed) {
  override def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology = ???
}

object CopiedOWLIndividual {

  class FactoryIQ(compatibilityMode: CompatibilityMode) { //(using ontologyManager: OWLOntologyManager) {

    private val lookupTableIQ = mutable.HashMap[(IQSaturationNode, RepairType), CopiedOWLIndividual]()

    def containsCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType): Boolean = {
      lookupTableIQ.contains((objectInTheSaturation, repairType))
    }

    def getCopyOrElseCreateCopyWithNamedIndividual(individualInTheSaturation: OWLNamedIndividual, repairType: RepairType) = {
      getOrElseCreateCopy(individualInTheSaturation, repairType, (_, _) => individualInTheSaturation)
    }

    def getCopyOrElseCreateCopyWithAnonymousIndividual(objectInTheSaturation: IQSaturationNode, repairType: RepairType) = {
      getOrElseCreateCopy(objectInTheSaturation, repairType, nextAnonymousIndividual)
    }

    private def getOrElseCreateCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType, objectInTheRepair: (IQSaturationNode, RepairType) => OWLIndividual) = {
      if !containsCopy(objectInTheSaturation, repairType) then
        lookupTableIQ((objectInTheSaturation, repairType)) = CopiedOWLIndividual(objectInTheSaturation, repairType, objectInTheRepair(objectInTheSaturation, repairType))
      lookupTableIQ((objectInTheSaturation, repairType))
    }

    private def nextAnonymousIndividual(objectInTheSaturation: IQSaturationNode, repairType: RepairType): OWLIndividual = {
      compatibilityMode match
        case NO =>
          AnonymousIndividual()
        case FRESH_NAMED_INDIVIDUALS =>
          // NamedIndividual(NodeID.nextAnonymousIRI())
          NamedIndividual("repair:variable#" + NodeID.nextAnonymousIRI().substring(2))
        case EXPLICIT_NAMED_INDIVIDUALS =>
          NamedIndividual("repair:variable#⟨" + toShortDLString(objectInTheSaturation) + "," + repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}") + "⟩")
    }

  }

//  final private class FactoryCQ private extends CopiedOWLIndividual.FactoryIQ {
//    final private val lookupTableCQ = HashMultimap.create
//
//    override private def newNamedIndividual(individualInTheSaturation: OWLIndividual, repairType: Nothing) = {
//      val copiedOWLIndividual = super.newNamedIndividual(individualInTheSaturation, repairType)
//      lookupTableCQ.put(individualInTheSaturation, copiedOWLIndividual)
//      copiedOWLIndividual
//    }
//
//    override private def newAnonymousIndividual(individualInTheSaturation: OWLIndividual, repairType: Nothing) = {
//      val copiedOWLIndividual = super.newAnonymousIndividual(individualInTheSaturation, repairType)
//      lookupTableCQ.put(individualInTheSaturation, copiedOWLIndividual)
//      copiedOWLIndividual
//    }
//
//    private def getCopiesOf(individualInTheSaturation: OWLIndividual) = Collections.unmodifiableCollection(lookupTableCQ.get(individualInTheSaturation))
//  }
}

final class CopiedOWLIndividual(val individualInTheSaturation: IQSaturationNode,  // t
                                val repairType: RepairType,                       // 𝒦
                                val individualInTheRepair: OWLIndividual) {       // y_{t,𝒦}

  /* The field 'individualInTheRepair' is intentionally not compared. */
  override def equals(that: Any): Boolean = {
    that match
      case that: CopiedOWLIndividual => (this.individualInTheSaturation equals that.individualInTheSaturation) && (this.repairType equals that.repairType)
      case _ => false
  }

  /* The field 'individualInTheRepair' is intentionally not hashed. */
  override def hashCode: Int = java.util.Objects.hash(individualInTheSaturation, repairType)

}

final class CopiedOWLObjectPropertyAssertionAxiom(val subject: CopiedOWLIndividual, val property: OWLObjectProperty, val target: CopiedOWLIndividual) {

  lazy val toAxiomInTheRepair = subject.individualInTheRepair Fact (property, target.individualInTheRepair)

  override def equals(that: Any): Boolean = {
    that match
      case that: CopiedOWLObjectPropertyAssertionAxiom => (this.subject equals that.subject) && (this.property equals that.property) && (this.target equals that.target)
      case _ => false
  }

  override def hashCode: Int = java.util.Objects.hash(subject, property, target)

}
