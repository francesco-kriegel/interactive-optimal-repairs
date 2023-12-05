package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Util.{AdditionallyIndexedOWLOntology, ImplicitOWLClassExpression, ImplicitOWLIndividual, ImplicitOWLObjectPropertyExpression}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*
import scala.util.hashing.MurmurHash3

sealed trait IQSaturationNode {
  lazy val toShortDLString: String
}

sealed trait IQSaturationShellPath {
  lazy val toIQSaturationNode: IQSaturationNode
  lazy val toShortDLString: String
  lazy val depth: Int
}

case class KernelObject(individual: OWLIndividual) extends IQSaturationNode, IQSaturationShellPath {
  lazy val toIQSaturationNode: IQSaturationNode = this
  lazy val toShortDLString: String = individual.toShortDLString
  lazy val depth: Int = 0
  override def equals(that: Any): Boolean =
    that match
      case KernelObject(jndividual) => individual equals jndividual
      case _ => false
  override def hashCode(): Int = individual.hashCode() * 2
}

case class ShellObject(classExpression: OWLClassExpression) extends IQSaturationNode {
  lazy val toShortDLString: String = classExpression.toShortDLString
  override def equals(that: Any): Boolean =
    that match
      case ShellObject(dlassExpression) => classExpression equals dlassExpression
      case _ => false
  override def hashCode(): Int = classExpression.hashCode() * 2
}

case class ProperShellPath(predecessor: IQSaturationShellPath, property: OWLObjectProperty, target: ShellObject) extends IQSaturationShellPath {
  lazy val toIQSaturationNode: IQSaturationNode = target
  lazy val toShortDLString: String = predecessor.toShortDLString + " ➔[" + property.toShortDLString + "]➔ " + target.toShortDLString
  lazy val depth: Int = predecessor.depth + 1
  override def equals(that: Any): Boolean =
    that match
      case ProperShellPath(qredecessor, qroperty, uarget) => (predecessor equals qredecessor) && (property equals qroperty) && (target equals uarget)
      case _ => false
  override def hashCode(): Int = MurmurHash3.productHash((predecessor, property, target))
}

type CQSaturationNode = IQSaturationShellPath

trait Saturation[N >: KernelObject](using configuration: RepairConfiguration) {

  def getSuccessors(node: N): collection.Set[(OWLObjectProperty, N)]
  def getLabels(node: N): collection.Set[OWLClass]
  def Succ(repairType: RepairType, property: OWLObjectProperty, target: N): collection.Set[OWLClassExpression]

  private lazy val allNodes = {
    val shellObjects = mutable.HashSet[N]()
    var nextShellObjects: collection.Set[N] =
      (configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
        concat configuration.ontology.getAnonymousIndividuals.asScala).map(KernelObject(_))
    while nextShellObjects.nonEmpty do
      shellObjects ++= nextShellObjects
      nextShellObjects = nextShellObjects.flatMap(getSuccessors(_).map(_._2)) diff shellObjects
    shellObjects
  }

  lazy val isAcyclic: Boolean = {

    var i = 0
    val index = mutable.HashMap[N, Int]()
    val lowlink = mutable.HashMap[N, Int]()
    val stack = mutable.Stack[N]()
    val isOnStack = mutable.HashSet[N]()
    val remainingNodes = mutable.HashSet.from[N](allNodes)

    var isAcyclic = !remainingNodes.exists(v => getSuccessors(v).map(_._2) contains v)

    def tarjan(v: N): Boolean = {
      index(v) = i
      lowlink(v) = i
      i += 1
      stack.push(v)
      isOnStack(v) = true
      remainingNodes.remove(v)
      var cycleDetected = false

      for (w <- getSuccessors(v).map(_._2) if !cycleDetected) {
        if remainingNodes contains w then
          if tarjan(w) then
            cycleDetected = true
          lowlink(v) = lowlink(v) min lowlink(w)
        else if isOnStack(w) then
          lowlink(v) = lowlink(v) min index(w)
      }
      if lowlink(v) equals index(v) then
        val scc = mutable.HashSet[N]()
        while {
          val w = stack.pop()
          isOnStack(w) = false
          scc.add(w)
          !(w equals v)
        } do ()
        cycleDetected |= scc.size > 1
      cycleDetected
    }

    while isAcyclic && remainingNodes.nonEmpty do
      if tarjan(remainingNodes.head) then
        isAcyclic = false
    isAcyclic

  }

}

class IQSaturation(using configuration: RepairConfiguration) extends Saturation[IQSaturationNode] {

  extension (node: IQSaturationNode) {
    infix def hasType(classExpression: OWLClassExpression)(using configuration: RepairConfiguration): Boolean = {
      node match
        case KernelObject(individualNode) =>
          // configuration.ontologyReasoner.types(individualNode) contains classExpression
          configuration.classificationOfInputOntology.isInstanceOf(individualNode, classExpression)
        case ShellObject(classExpressionNode) =>
          // configuration.ontologyReasoner.subsumers(classExpressionNode) contains classExpression
          configuration.classificationOfInputOntology.isSubsumedBy(classExpressionNode, classExpression)
    }
  }

  private val tboxSuccessors = mutable.HashMap[OWLClassExpression, mutable.HashSet[(OWLObjectProperty, ShellObject)]]()
  configuration.conceptInclusions.foreach {
    case SubClassOf(_, subClass, superClass) =>
      tboxSuccessors.getOrElseUpdate(subClass, { mutable.HashSet[(OWLObjectProperty, ShellObject)]() })
        ++= superClass.topLevelConjuncts().collect { case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, ShellObject(filler)) }
    case _ => // Do nothing.
  }

  override def getSuccessors(node: IQSaturationNode): collection.Set[(OWLObjectProperty, IQSaturationNode)] = {
    node match
      case KernelObject(individual) =>
//        configuration.ontology.getABoxAxioms(Imports.INCLUDED).asScala.collect[(OWLObjectProperty, IQSaturationNode)] {
//          case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, target) if subject equals individual => (property, target)
//          case ClassAssertion(_, ObjectSomeValuesFrom(property@ObjectProperty(_), filler), jndividual) if individual equals jndividual => (property, filler)
//        } ++ configuration.ontologyReasoner.types(individual).filter(tboxSuccessors.keySet).flatMap(tboxSuccessors)
        configuration.ontology.getObjectPropertyAssertionAxioms(individual).asScala.map({ case ObjectPropertyAssertion(_, property@ObjectProperty(_), _, target) => (property, KernelObject(target)) }) ++
          configuration.ontology.getClassAssertionAxioms(individual).asScala.flatMap({ case ClassAssertion(_, classExpression, _) => classExpression.asConjunctSet().asScala.filter(_.isObjectSomeValuesFrom).map({ case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, ShellObject(filler)) }) }) ++
          configuration.classificationOfInputOntology.types(individual).filter(tboxSuccessors.keySet).flatMap(tboxSuccessors)
      case ShellObject(classExpression) =>
        classExpression.getTopLevelConjuncts.collect[(OWLObjectProperty, IQSaturationNode)] {
          case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, ShellObject(filler))
        } ++ configuration.classificationOfInputOntology.subsumers(classExpression).filter(tboxSuccessors.keySet).flatMap(tboxSuccessors)
  }

  override def getLabels(node: IQSaturationNode): collection.Set[OWLClass] = {
    node match
      case KernelObject(individual) =>
        configuration.classificationOfInputOntology.types(individual).collect { case c@Class(_) => c }.toSet
      case ShellObject(classExpression) =>
        configuration.classificationOfInputOntology.subsumers(classExpression).collect { case c@Class(_) => c }.toSet
  }

  override def Succ(repairType: RepairType, property: OWLObjectProperty, target: IQSaturationNode): collection.Set[OWLClassExpression] = {
//    val succ = repairType.atoms.collect {
//      //      case ObjectSomeValuesFrom(qroperty, nominal@Nominal(uarget)) => if (property equals qroperty) && (target equals uarget) then nominal
//      //      case ObjectSomeValuesFrom(qroperty, filler) => if (property equals qroperty) && (target hasType filler) then filler
//      //      case ObjectHasValue(qroperty, uarget@NamedIndividual(_)) => if (property equals qroperty) && (target equals uarget) then Nominal(uarget)
//      case ObjectSomeValuesFrom(qroperty, filler) if (property equals qroperty) && (target hasType filler) => filler
//    }
//    val types =
//      target match
//        case individual: OWLIndividual => Set.from(configuration.ontologyReasoner.types(individual))
//        case classExpression: OWLClassExpression => Set.from(configuration.ontologyReasoner.subsumers(classExpression))
//    if !(succ subsetOf types) then
//      Console.err.println("Repair type: " + repairType.atoms.map(_.toShortDLString).mkString("{", ",", "}"))
//      Console.err.println("Property: " + property.toShortDLString)
//      Console.err.println("Target node: " + target.toShortDLString)
//      Console.err.println("Computed Succ: " + succ.map(_.toShortDLString).mkString("{", ",", "}"))
//      Console.err.println("Types: " + types.map(_.toShortDLString).mkString("{", ",", "}"))
//      throw RuntimeException() // sanity check, could be removed
//    succ
    repairType.atoms.collect {
      case ObjectSomeValuesFrom(qroperty, filler) if (property equals qroperty) && (target hasType filler) => filler
    }
  }

  private lazy val allShellObjects = {
    val shellObjects = mutable.HashSet[ShellObject]()
    var nextShellObjects: collection.Set[ShellObject] =
      (configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
        concat configuration.ontology.getAnonymousIndividuals.asScala).flatMap {
        individual => getSuccessors(KernelObject(individual)).collect { case (_, target@ShellObject(_)) => target } }
    while nextShellObjects.nonEmpty do
      shellObjects ++= nextShellObjects
      nextShellObjects = nextShellObjects.flatMap(getSuccessors(_).map(_._2.asInstanceOf[ShellObject])) diff shellObjects
    shellObjects
  }

  lazy val hasAcyclicShell: Boolean = {

    var i = 0
    val index = mutable.HashMap[ShellObject, Int]()
    val lowlink = mutable.HashMap[ShellObject, Int]()
    val stack = mutable.Stack[ShellObject]()
    val isOnStack = mutable.HashSet[ShellObject]()
    val remainingNodes = mutable.HashSet.from[ShellObject](allShellObjects)

    var isAcyclic = !remainingNodes.exists(v => getSuccessors(v).map(_._2) contains v)

    def tarjan(v: ShellObject): Boolean = {
      index(v) = i
      lowlink(v) = i
      i += 1
      stack.push(v)
      isOnStack(v) = true
      remainingNodes.remove(v)
      var cycleDetected = false

      for (w <- getSuccessors(v).map(_._2.asInstanceOf[ShellObject]) if !cycleDetected) {
        if remainingNodes contains w then
          if tarjan(w) then
            cycleDetected = true
          lowlink(v) = lowlink(v) min lowlink(w)
        else if isOnStack(w) then
          lowlink(v) = lowlink(v) min index(w)
      }
      if lowlink(v) equals index(v) then
        val scc = mutable.HashSet[ShellObject]()
        while {
          val w = stack.pop()
          isOnStack(w) = false
          scc.add(w)
          !(w equals v)
        } do ()
        cycleDetected |= scc.size > 1
      cycleDetected
    }

    while isAcyclic && remainingNodes.nonEmpty do
      if tarjan(remainingNodes.head) then
        isAcyclic = false
    isAcyclic

  }

}

class NoIQSaturation(using configuration: RepairConfiguration) extends Saturation[IQSaturationNode] {

  extension (node: IQSaturationNode) {
    infix def hasType(classExpression: OWLClassExpression)(using configuration: RepairConfiguration): Boolean = {
      node match
        case KernelObject(individualNode) =>
          // configuration.trivialReasoner.types(individualNode) contains classExpression
          configuration.classificationOfEmptyOntology.isInstanceOf(individualNode, classExpression)
        case ShellObject(classExpressionNode) =>
          // configuration.trivialReasoner.subsumers(classExpressionNode) contains classExpression
          configuration.classificationOfEmptyOntology.isSubsumedBy(classExpressionNode, classExpression)
    }
  }

  override def getSuccessors(node: IQSaturationNode): collection.Set[(OWLObjectProperty, IQSaturationNode)] = {
    node match
      case KernelObject(individual) =>
//        /* TODO: Make the below method more efficient by employing the indexes maintained by the OWLAPI in `configuration.ontology` */
//        configuration.ontology.getABoxAxioms(Imports.INCLUDED).asScala.collect {
//          case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, target) if subject equals individual => (property, target)
//          case ClassAssertion(_, ObjectSomeValuesFrom(property@ObjectProperty(_), filler), jndividual) if individual equals jndividual => (property, filler)
//        }
        configuration.ontology.getObjectPropertyAssertionAxioms(individual).asScala.map({ case ObjectPropertyAssertion(_, property@ObjectProperty(_), _, target) => (property, KernelObject(target)) }) ++
          configuration.ontology.getClassAssertionAxioms(individual).asScala.flatMap({ case ClassAssertion(_, classExpression, _) => classExpression.asConjunctSet().asScala.filter(_.isObjectSomeValuesFrom).map({ case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, ShellObject(filler)) }) })
      case ShellObject(classExpression) =>
        classExpression.getTopLevelConjuncts.collect {
          case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, ShellObject(filler))
        }
  }

  override def getLabels(node: IQSaturationNode): collection.Set[OWLClass] = {
    node match
      case KernelObject(individual) =>
//        configuration.ontology.getABoxAxioms(Imports.INCLUDED).asScala.collect {
//          case ClassAssertion(_, clazz @ Class(_), jndividual) if individual equals jndividual => clazz
//        }
        configuration.ontology.getClassAssertionAxioms(individual).asScala.flatMap({ case ClassAssertion(_, classExpression, _) => classExpression.asConjunctSet().asScala.filter(_.isClass).map(_.asOWLClass) })
      case ShellObject(classExpression) =>
        classExpression.getTopLevelConjuncts.filter(_.isClass).map(_.asOWLClass())
  }

  override def Succ(repairType: RepairType, property: OWLObjectProperty, target: IQSaturationNode): collection.Set[OWLClassExpression] = {
    repairType.atoms.collect {
      case ObjectSomeValuesFrom(qroperty, filler) if (property equals qroperty) && (target hasType filler) => filler
    }
  }

}

trait HasPredecessors[N] {
  def getPredecessors(node: N): collection.Set[(OWLObjectProperty, N)]
}

abstract class ShellUnfolding(val iqSaturation: IQSaturation | NoIQSaturation)(using configuration: RepairConfiguration) extends Saturation[CQSaturationNode] with HasPredecessors[CQSaturationNode] {

  lazy val isFinite: Boolean

  def getSuccessors(node: CQSaturationNode): collection.Set[(OWLObjectProperty, CQSaturationNode)] = {
    iqSaturation.getSuccessors(node.toIQSaturationNode).map {
      case (property, target@KernelObject(_)) => (property, target)
      case (property, target@ShellObject(_)) => (property, ProperShellPath(node, property, target))
    }
  }

  private lazy val ontology = AdditionallyIndexedOWLOntology(configuration.ontology)

  def getPredecessors(node: CQSaturationNode): collection.Set[(OWLObjectProperty, CQSaturationNode)] = {
    node match
      case KernelObject(individual) =>
        ontology.objectPropertyAssertionAxiomsWithObject(individual).toScala(LazyList)
          .map { case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, _) => (property, KernelObject(subject)) }
          .toSet
      case ProperShellPath(predecessor, property, _) =>
        Set((property, predecessor))
  }

  def getLabels(node: CQSaturationNode): collection.Set[OWLClass] = {
    iqSaturation.getLabels(node.toIQSaturationNode)
  }

  def Succ(repairType: RepairType, property: OWLObjectProperty, target: CQSaturationNode): collection.Set[OWLClassExpression] = {
    iqSaturation.Succ(repairType, property, target.toIQSaturationNode)
  }

  override lazy val isAcyclic: Boolean = {

    var i = 0
    val index = mutable.HashMap[KernelObject, Int]()
    val lowlink = mutable.HashMap[KernelObject, Int]()
    val stack = mutable.Stack[KernelObject]()
    val isOnStack = mutable.HashSet[KernelObject]()
    val remainingNodes = mutable.HashSet.from[KernelObject](
      (configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
        concat configuration.ontology.getAnonymousIndividuals.asScala).map(KernelObject(_)))

    var isAcyclic = !remainingNodes.exists(v => getSuccessors(v).map(_._2) contains v)

    def tarjan(v: KernelObject): Boolean = {
      index(v) = i
      lowlink(v) = i
      i += 1
      stack.push(v)
      isOnStack(v) = true
      remainingNodes.remove(v)
      var cycleDetected = false

      for (w <- getSuccessors(v).map(_._2).filter(_.isInstanceOf[KernelObject]).map(_.asInstanceOf[KernelObject]) if !cycleDetected) {
        if remainingNodes contains w then
          if tarjan(w) then
            cycleDetected = true
          lowlink(v) = lowlink(v) min lowlink(w)
        else if isOnStack(w) then
          lowlink(v) = lowlink(v) min index(w)
      }
      if lowlink(v) equals index(v) then
        val scc = mutable.HashSet[KernelObject]()
        while {
          val w = stack.pop()
          isOnStack(w) = false
          scc.add(w)
          !(w equals v)
        } do ()
        cycleDetected |= scc.size > 1
      cycleDetected
    }

    while isAcyclic && remainingNodes.nonEmpty do
      if tarjan(remainingNodes.head) then
        isAcyclic = false
    isAcyclic

  }

}

class CQSaturation(using configuration: RepairConfiguration) extends ShellUnfolding(configuration.iqSaturation) {

  override lazy val isFinite: Boolean = configuration.iqSaturation.hasAcyclicShell

}

class NoCQSaturation(using configuration: RepairConfiguration) extends ShellUnfolding(NoIQSaturation()) {

  override lazy val isFinite: Boolean = true

}
