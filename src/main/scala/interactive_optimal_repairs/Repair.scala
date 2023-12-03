package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.CompatibilityMode.*
import interactive_optimal_repairs.ImplicitIQSaturationNode
import interactive_optimal_repairs.QueryLanguage.*
import interactive_optimal_repairs.Util.{ImplicitIterableOfOWLClassExpressions, ImplicitOWLClassExpression, Nominal}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import scala.collection.mutable
import scala.jdk.CollectionConverters.*

enum CompatibilityMode(val description: String) {
  case NO extends CompatibilityMode("Use anonymous individuals (default mode)")
  case FRESH_NAMED_INDIVIDUALS extends CompatibilityMode("Use fresh named individuals (compatibility mode)")
  case EXPLICIT_NAMED_INDIVIDUALS extends CompatibilityMode("Use named individuals that indicate the pair in the formal construction (inspection mode, do not use in production)")
}

object Repair {

  def apply(queryLanguage: QueryLanguage, seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager): Repair = {
    queryLanguage match
      case IQ => IQRepair(seed)
      case IRQ => IRQRepair(seed)
      case CQ => CQRepair(seed)
  }

}

trait Repair(val seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration) {

//  private lazy val saturation = if saturated then IQSaturation() else ???
  private lazy val saturation = if saturated then configuration.iqSaturation else ???

  def entails(query: Query): Boolean = {
    if saturated then
      query match
        case classAssertion @ ClassAssertion(_, classExpression, individual @ NamedIndividual(_)) if ELExpressivityChecker.checkClassExpression(classExpression) =>
          (configuration.ontologyReasoner entails classAssertion)
            && !(classExpression isCoveredBy seed(individual) wrt configuration.ontologyReasoner)
        case roleAssertion @ ObjectPropertyAssertion(_, property @ ObjectProperty(_), subject @ NamedIndividual(_), target @ NamedIndividual(_)) =>
          (configuration.ontology containsAxiom roleAssertion)
            && !(configuration.request.negativeAxioms contains roleAssertion)
            && (saturation.Succ(seed(subject), property, target) isCoveredBy seed(target) wrt configuration.trivialReasoner)
        case _ => ???
    else
      ???
  }

  def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology

}

class IQRepair(seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends Repair(seed, saturated) {

  override def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology = {
//    val saturation = if saturated then IQSaturation() else NoSaturation()
    val saturation = if saturated then configuration.iqSaturation else NoSaturation()
    val repair = ontologyManager.createOntology()
    ontologyManager.addAxioms(repair, configuration.ontology.getTBoxAxioms(Imports.INCLUDED))
    val factory = CopiedOWLIndividual.FactoryIQ(compatibilityMode)
    val queue = mutable.Queue[CopiedOWLIndividual]()
    configuration.ontology.getABoxAxioms(Imports.INCLUDED).asScala foreach {
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        if saturation.Succ(seed(subject), property, target) isCoveredBy seed(target) wrt configuration.trivialReasoner then
          ontologyManager.addAxiom(repair, subject Fact (property, target))
      case _ => // Do nothing.
    }
    configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
      .map(individual => factory.getCopyOrElseCreateCopyWithNamedIndividual(individual, seed.getRepairType(individual)))
      .foreach(queue.enqueue)
    while queue.nonEmpty do
      val subject = queue.dequeue()
      saturation.getLabels(subject.individualInTheSaturation)
        .filterNot(subject.repairType.atoms.contains)
        .map(subject.individualInTheRepair Type _)
        .foreach(ontologyManager.addAxiom(repair, _))
      saturation.getSuccessors(subject.individualInTheSaturation)
        .foreach { (property, targetInTheSaturation) =>
          RepairType.computeAllMinimalRepairTypes(targetInTheSaturation, saturation.Succ(subject.repairType, property, targetInTheSaturation))
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

class IRQRepair(seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager)
  extends IQRepair({
    val newAxioms = mutable.HashSet.from[OWLClassAssertionAxiom](seed.axioms)
    configuration.request.negativeAxioms foreach {
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        // newAxioms += (subject Type (property some Nominal(target))) // standard translation of role assertions into class assertions, as used in the KR 2022 paper
        val nominal = Nominal(target)
        val successor = property some nominal
        newAxioms += (subject Type successor) // standard translation of role assertions into class assertions, as used in the KR 2022 paper
        configuration.trivialReasoner.addClassExpression(nominal)
        configuration.trivialReasoner.addClassExpression(successor)
        configuration.ontologyReasoner.addClassExpression(nominal)
        configuration.ontologyReasoner.addClassExpression(successor)
      case _ => // Do nothing.
    }
    RepairSeed(seed.preprocessed, newAxioms)
  }, saturated) {}

class CQRepair(seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration) extends Repair(seed, saturated) {
  override def compute(compatibilityMode: CompatibilityMode = NO): OWLOntology = ???
}

object CopiedOWLIndividual {

  class FactoryIQ(compatibilityMode: CompatibilityMode) { //(using ontologyManager: OWLOntologyManager) {

    private val lookupTableIQ = mutable.HashMap[(IQSaturationNode, RepairType), CopiedOWLIndividual]()

    def containsCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType): Boolean = {
      lookupTableIQ.contains((objectInTheSaturation, repairType))
    }

    def getCopyOrElseCreateCopyWithNamedIndividual(individualInTheSaturation: OWLNamedIndividual, repairType: RepairType): CopiedOWLIndividual = {
      getOrElseCreateCopy(individualInTheSaturation, repairType, (_, _) => individualInTheSaturation)
    }

    def getCopyOrElseCreateCopyWithAnonymousIndividual(objectInTheSaturation: IQSaturationNode, repairType: RepairType): CopiedOWLIndividual = {
      getOrElseCreateCopy(objectInTheSaturation, repairType, nextAnonymousIndividual)
    }

    private def getOrElseCreateCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType, objectInTheRepair: (IQSaturationNode, RepairType) => OWLIndividual): CopiedOWLIndividual = {
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
          NamedIndividual("repair:variable#⟨" + objectInTheSaturation.toShortDLString + "," + repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}") + "⟩")
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

  override def toString: String = "⟪" + individualInTheSaturation + "," + repairType + "⟫"

}

final class CopiedOWLObjectPropertyAssertionAxiom(val subject: CopiedOWLIndividual, val property: OWLObjectProperty, val target: CopiedOWLIndividual) {

  lazy val toAxiomInTheRepair: OWLObjectPropertyAssertionAxiom = subject.individualInTheRepair Fact (property, target.individualInTheRepair)

  override def equals(that: Any): Boolean = {
    that match
      case that: CopiedOWLObjectPropertyAssertionAxiom => (this.subject equals that.subject) && (this.property equals that.property) && (this.target equals that.target)
      case _ => false
  }

  override def hashCode: Int = java.util.Objects.hash(subject, property, target)

}
