package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.CompatibilityMode.*
import interactive_optimal_repairs.QueryLanguage.*
import interactive_optimal_repairs.Util.{ImplicitBoolean, ImplicitIterableOfOWLClassExpressions, ImplicitOWLClassExpression, Nominal}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.reflect.ClassTag

enum CompatibilityMode(val description: String) {
  case NO extends CompatibilityMode("Use anonymous individuals (default mode)")
  case FRESH_NAMED_INDIVIDUALS extends CompatibilityMode("Use fresh named individuals (compatibility mode)")
  case EXPLICIT_NAMED_INDIVIDUALS extends CompatibilityMode("Use named individuals that indicate the pair in the formal construction (inspection mode, do not use in production)")
}

object Repair {

  def apply(queryLanguage: QueryLanguage, seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager): Repair = {
    queryLanguage match
      case IRQ => IRQRepair(seed, saturated)
      case CQ => CQRepair(seed, saturated)
  }

}

trait Repair(protected val seed: RepairSeed, protected val saturated: Boolean = true)(using configuration: RepairConfiguration) {

  protected lazy val iqSaturation: IQSaturation | NoIQSaturation = if saturated then configuration.iqSaturation else NoIQSaturation()
  lazy val isFinite: Boolean

  def entails(query: Query): Boolean = {
    if saturated then
      query match
        case classAssertion @ ClassAssertion(_, classExpression, individual @ NamedIndividual(_)) if ELExpressivityChecker.checkClassExpression(classExpression) =>
          (configuration.classificationOfInputOntology entails classAssertion)
            && !(classExpression isCoveredBy seed(individual) wrt configuration.classificationOfInputOntology)
        case roleAssertion @ ObjectPropertyAssertion(_, property @ ObjectProperty(_), subject @ NamedIndividual(_), target @ NamedIndividual(_)) =>
          (configuration.ontology containsAxiom roleAssertion)
            && !(configuration.request.negativeAxioms contains roleAssertion)
            && (iqSaturation.Succ(seed(subject), property, KernelObject(target)) isCoveredBy seed(target) wrt configuration.classificationOfEmptyOntology)
        case _ => ???
    else
      ???
  }

  def compute(compatibilityMode: CompatibilityMode = NO, depth: Option[Int] = None): OWLOntology

}

private class IRQRepair(seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager)
  extends Repair(seed, saturated) {

  lazy val isFinite: Boolean = true

  override def compute(compatibilityMode: CompatibilityMode = NO, depth: Option[Int] = None): OWLOntology = {
    val repair = ontologyManager.createOntology()
    ontologyManager.addAxioms(repair, configuration.ontology.getTBoxAxioms(Imports.INCLUDED))

    val lookupTableIQ = mutable.HashMap[(IQSaturationNode, RepairType), Copy[IQSaturationNode]]()
    def containsCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType): Boolean = {
      lookupTableIQ.contains((objectInTheSaturation, repairType))
    }
    def getCopyOrElseCreateCopyWithNamedIndividual(individualInTheSaturation: OWLNamedIndividual, repairType: RepairType): Copy[IQSaturationNode] = {
      getOrElseCreateCopy(KernelObject(individualInTheSaturation), repairType, (_, _) => individualInTheSaturation)
    }
    def getCopyOrElseCreateCopyWithAnonymousIndividual(objectInTheSaturation: IQSaturationNode, repairType: RepairType): Copy[IQSaturationNode] = {
      getOrElseCreateCopy(objectInTheSaturation, repairType, nextAnonymousIndividual)
    }
    def getOrElseCreateCopy(objectInTheSaturation: IQSaturationNode, repairType: RepairType, objectInTheRepair: (IQSaturationNode, RepairType) => OWLIndividual): Copy[IQSaturationNode] = {
      val maybeCopy = lookupTableIQ.get((objectInTheSaturation, repairType))
      if maybeCopy.isDefined then
        maybeCopy.get
      else
        val copy = Copy(objectInTheSaturation, repairType, objectInTheRepair(objectInTheSaturation, repairType))
        lookupTableIQ((objectInTheSaturation, repairType)) = copy
        copy
    }
    def nextAnonymousIndividual(objectInTheSaturation: IQSaturationNode, repairType: RepairType): OWLIndividual = {
      compatibilityMode match
        case NO =>
          AnonymousIndividual()
        case FRESH_NAMED_INDIVIDUALS =>
          // NamedIndividual(NodeID.nextAnonymousIRI())
          NamedIndividual("repair:variable#" + NodeID.nextAnonymousIRI().substring(2))
        case EXPLICIT_NAMED_INDIVIDUALS =>
          NamedIndividual("repair:variable#⟨" + objectInTheSaturation.toShortDLString + ", " + (if repairType.atoms.isEmpty then "∅" else repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}")) + "⟩")
    }

    val queue = mutable.Queue[Copy[IQSaturationNode]]()
    configuration.ontology.getABoxAxioms(Imports.INCLUDED).asScala foreach {
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        if iqSaturation.Succ(seed(subject), property, KernelObject(target)) isCoveredBy seed(target) wrt configuration.classificationOfEmptyOntology then
          ontologyManager.addAxiom(repair, subject Fact (property, target))
      case _ => // Do nothing.
    }
    configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
      .map(individual => getCopyOrElseCreateCopyWithNamedIndividual(individual, seed.getRepairType(individual)))
      .foreach(queue.enqueue)
    while queue.nonEmpty do
      val subject = queue.dequeue()
      iqSaturation.getLabels(subject.objectInTheSaturation)
        .filterNot(subject.repairType.atoms.contains)
        .map(subject.objectInTheRepair Type _)
        .foreach(ontologyManager.addAxiom(repair, _))
      iqSaturation.getSuccessors(subject.objectInTheSaturation)
        .foreach { (property, targetInTheSaturation) =>
          RepairType.computeAllMinimalRepairTypes(targetInTheSaturation, iqSaturation.Succ(subject.repairType, property, targetInTheSaturation))
            .foreach { repairType =>
              val targetAlreadyExists = containsCopy(targetInTheSaturation, repairType)
              val target = getCopyOrElseCreateCopyWithAnonymousIndividual(targetInTheSaturation, repairType)
              ontologyManager.addAxiom(repair, subject.objectInTheRepair Fact (property, target.objectInTheRepair))
              if !targetAlreadyExists then queue.enqueue(target)
            }
        }
    repair
  }

}

private class CQRepair(seed: RepairSeed, saturated: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager)
  extends Repair(seed, saturated) {

  private lazy val cqSaturation = if saturated then CQSaturation() else NoCQSaturation()
  lazy val isFinite: Boolean = saturated implies configuration.iqSaturation.hasAcyclicShell

  def compute(compatibilityMode: CompatibilityMode = NO, depth: Option[Int] = None): OWLOntology = {
    val repair = ontologyManager.createOntology()
    ontologyManager.addAxioms(repair, configuration.ontology.getTBoxAxioms(Imports.INCLUDED))

    val lookupTableIQ = mutable.HashMap[(CQSaturationNode, RepairType), Copy[CQSaturationNode]]()
    val lookupTableCQ = mutable.HashMap[CQSaturationNode, mutable.HashSet[Copy[CQSaturationNode]]]()

    def containsCopy(objectInTheSaturation: CQSaturationNode, repairType: RepairType): Boolean = {
      lookupTableIQ.contains((objectInTheSaturation, repairType))
    }
    def getCopyOrElseCreateCopyWithNamedIndividual(individualInTheSaturation: OWLNamedIndividual, repairType: RepairType): Copy[CQSaturationNode] = {
      getOrElseCreateCopy(KernelObject(individualInTheSaturation), repairType, (_, _) => individualInTheSaturation)
    }
    def getCopyOrElseCreateCopyWithAnonymousIndividual(objectInTheSaturation: CQSaturationNode, repairType: RepairType): Copy[CQSaturationNode] = {
      getOrElseCreateCopy(objectInTheSaturation, repairType, nextAnonymousIndividual)
    }
    def getOrElseCreateCopy(objectInTheSaturation: CQSaturationNode, repairType: RepairType, objectInTheRepair: (CQSaturationNode, RepairType) => OWLIndividual): Copy[CQSaturationNode] = {
      val maybeCopy = lookupTableIQ.get((objectInTheSaturation, repairType))
      if maybeCopy.isDefined then
        maybeCopy.get
      else
        val copy = Copy(objectInTheSaturation, repairType, objectInTheRepair(objectInTheSaturation, repairType))
        lookupTableIQ((objectInTheSaturation, repairType)) = copy
        lookupTableCQ.getOrElseUpdate(objectInTheSaturation, { mutable.HashSet[Copy[CQSaturationNode]]() }) += copy
        copy
    }
    def nextAnonymousIndividual(objectInTheSaturation: CQSaturationNode, repairType: RepairType): OWLIndividual = {
      compatibilityMode match
        case NO =>
          AnonymousIndividual()
        case FRESH_NAMED_INDIVIDUALS =>
          // NamedIndividual(NodeID.nextAnonymousIRI())
          NamedIndividual("repair:variable#" + NodeID.nextAnonymousIRI().substring(2))
        case EXPLICIT_NAMED_INDIVIDUALS =>
          NamedIndividual("repair:variable#⟨" + objectInTheSaturation.toShortDLString + ", " + (if repairType.atoms.isEmpty then "∅" else repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}")) + "⟩")
    }


    val queue = mutable.Queue[AssertionCopy[CQSaturationNode]]()

    def addNewCopyToTheRepair(copy: Copy[CQSaturationNode]): Unit = {
      cqSaturation.getLabels(copy.objectInTheSaturation)
        .filterNot(copy.repairType.atoms.contains)
        .map(copy.objectInTheRepair Type _)
        .foreach(ontologyManager.addAxiom(repair, _))
      cqSaturation.getSuccessors(copy.objectInTheSaturation).foreach { case (property, target) =>
        getCopiesOf(target).foreach { copyOfTarget =>
          queue.enqueue(AssertionCopy[CQSaturationNode](copy, property, copyOfTarget))
        }
      }
      cqSaturation.getPredecessors(copy.objectInTheSaturation).foreach { case (property, subject) =>
        getCopiesOf(subject).foreach { copyOfSubject =>
          if !(copy equals copyOfSubject) then
            queue.enqueue(AssertionCopy[CQSaturationNode](copyOfSubject, property, copy))
        }
      }
    }

    configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala.foreach({ individual =>
      addNewCopyToTheRepair(getCopyOrElseCreateCopyWithNamedIndividual(individual, seed(individual)))
      if seed(individual).atoms.nonEmpty then
        addNewCopyToTheRepair(getCopyOrElseCreateCopyWithAnonymousIndividual(KernelObject(individual), RepairType(KernelObject(individual), Set.empty)))
    })
    configuration.ontology.getAnonymousIndividuals.asScala.foreach({ individual =>
      addNewCopyToTheRepair(getCopyOrElseCreateCopyWithAnonymousIndividual(KernelObject(individual), RepairType(KernelObject(individual), Set.empty)))
    })

    def getCopiesOf(objectInTheSaturation: CQSaturationNode): collection.Set[Copy[CQSaturationNode]] = {
      //lookupTableCQ.getOrElse(objectInTheSaturation, Set.empty)
      if depth.isDefined && objectInTheSaturation.depth > depth.get then
        Set.empty
      else
        if !(lookupTableCQ contains objectInTheSaturation) then
          addNewCopyToTheRepair(getCopyOrElseCreateCopyWithAnonymousIndividual(objectInTheSaturation, RepairType(objectInTheSaturation.toIQSaturationNode, Set.empty)))
        lookupTableCQ(objectInTheSaturation)
    }

    while queue.nonEmpty do {
      val assertionCopy = queue.dequeue()
      val subject = assertionCopy.subject
      val property = assertionCopy.property
      val target = assertionCopy.target
      if depth.isDefined implies target.objectInTheSaturation.depth <= depth.get then
        val Succ = cqSaturation.Succ(subject.repairType, property, target.objectInTheSaturation)
        if Succ isCoveredBy target.repairType wrt configuration.classificationOfEmptyOntology then
          ontologyManager.addAxiom(repair, assertionCopy.toAxiomInTheRepair)
        else
          RepairType.computeAllMinimalRepairTypes(target.objectInTheSaturation.toIQSaturationNode, target.repairType.atoms union Succ)
            .foreach { repairType =>
              if !containsCopy(target.objectInTheSaturation, repairType) then
                addNewCopyToTheRepair(getCopyOrElseCreateCopyWithAnonymousIndividual(target.objectInTheSaturation, repairType))
            }
    }

    repair
  }

}

private final class Copy[N : ClassTag](val objectInTheSaturation: N,          // t
                                       val repairType: RepairType,            // 𝒦
                                       val objectInTheRepair: OWLIndividual)  // ⟪t,𝒦⟫
                                      (implicit classTag_Copy_N: ClassTag[Copy[N]]) {

  /* The field 'objectInTheRepair' is intentionally not compared. */
  override def equals(that: Any): Boolean = {
    that match
//      case that: CopiedOWLIndividual[N]
      case classTag_Copy_N(that) => (this.objectInTheSaturation equals that.objectInTheSaturation) && (this.repairType equals that.repairType)
      case _ => false
  }

  /* The field 'objectInTheRepair' is intentionally not hashed. */
  override def hashCode: Int = java.util.Objects.hash(objectInTheSaturation, repairType)

  override def toString: String = "⟪" + objectInTheSaturation + "," + repairType + "⟫"

}

private final class AssertionCopy[N : ClassTag](val subject: Copy[N],
                                                val property: OWLObjectProperty,
                                                val target: Copy[N])
                                               (implicit classTag_AssertionCopy_N: ClassTag[AssertionCopy[N]]) {

  lazy val toAxiomInTheRepair: OWLObjectPropertyAssertionAxiom = subject.objectInTheRepair Fact (property, target.objectInTheRepair)

  override def equals(that: Any): Boolean = {
    that match
//      case that: AssertionCopy[N] =>
      case classTag_AssertionCopy_N(that) => (this.subject equals that.subject) && (this.property equals that.property) && (this.target equals that.target)
      case _ => false
  }

  override def hashCode: Int = java.util.Objects.hash(subject, property, target)

}
