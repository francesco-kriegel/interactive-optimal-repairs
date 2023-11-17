package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.IQSaturationNode.toShortDLString
import interactive_optimal_repairs.Util.{ImplicitOWLClassExpression, ImplicitOWLIndividual, ImplicitOWLObjectPropertyExpression}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*

import scala.collection.mutable

trait Saturation[N >: OWLIndividual](using configuration: RepairConfiguration) {

  def getSuccessors(node: N): Iterable[(OWLObjectProperty, N)]
  def getLabels(node: N): Iterable[OWLClass]
  def Succ(repairType: RepairType, property: OWLObjectProperty, target: N): collection.Set[OWLClassExpression]

  lazy val isAcyclic: Boolean = {

    var isAcyclic = true

    var i = 0
    val index = mutable.HashMap[N, Int]()
    val lowlink = mutable.HashMap[N, Int]()
    val stack = mutable.Stack[N]()
    val isOnStack = mutable.HashSet[N]()
    val remainingNodes = mutable.HashSet[N]()

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

    def tarjan(v: N): Boolean = {
      index(v) = i
      lowlink(v) = i
      i += 1
      stack.push(v)
      isOnStack(v) = true
      remainingNodes.remove(v)

      val forLoop = new scala.util.control.Breaks
      forLoop.tryBreakable {
        for (w <- getSuccessors(v).map(_._2)) {
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
          val scc = mutable.HashSet[N]()
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

type IQSaturationNode = OWLIndividual | OWLClassExpression

object IQSaturationNode {

  extension (node: IQSaturationNode) {
    def toShortDLString(): String = {
      node match
        case individual: OWLIndividual => individual.toShortDLString
        case classExpression: OWLClassExpression => classExpression.toShortDLString
    }
  }

}

class IQSaturation(using configuration: RepairConfiguration) extends Saturation[IQSaturationNode] {

  extension (node: IQSaturationNode) {
    infix def hasType(classExpression: OWLClassExpression)(using configuration: RepairConfiguration): Boolean = {
      node match
        case individualNode: OWLIndividual => configuration.ontologyReasoner.types(individualNode) contains classExpression
        case classExpressionNode: OWLClassExpression => configuration.ontologyReasoner.subsumers(classExpressionNode) contains classExpression
    }
  }

  private val tboxSuccessors = mutable.HashMap[OWLClassExpression, mutable.HashSet[(OWLObjectProperty, OWLClassExpression)]]()
  configuration.axioms.foreach {
    case SubClassOf(_, subClass, superClass) =>
      tboxSuccessors.getOrElseUpdate(subClass, {
        mutable.HashSet[(OWLObjectProperty, OWLClassExpression)]()
      }) ++= superClass.topLevelConjuncts().collect { case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, filler) }
    case _ => // Do nothing.
  }

  override def getSuccessors(node: IQSaturationNode): Iterable[(OWLObjectProperty, IQSaturationNode)] = {
    node match
      case individual: OWLIndividual =>
        configuration.axioms.collect[(OWLObjectProperty, IQSaturationNode)] {
          case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, target) if subject equals individual => (property, target)
          case ClassAssertion(_, ObjectSomeValuesFrom(property@ObjectProperty(_), filler), jndividual) if individual equals jndividual => (property, filler)
        } ++ configuration.ontologyReasoner.types(individual).filter(tboxSuccessors.keySet).flatMap(tboxSuccessors)
      case classExpression: OWLClassExpression =>
        classExpression.topLevelConjuncts().collect[(OWLObjectProperty, IQSaturationNode)] {
          case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, filler)
        } ++ configuration.ontologyReasoner.subsumers(classExpression).filter(tboxSuccessors.keySet).flatMap(tboxSuccessors)
  }

  override def getLabels(node: IQSaturationNode): Iterable[OWLClass] = {
    node match
      case individual: OWLIndividual =>
        configuration.ontologyReasoner.types(individual).collect { case c@Class(_) => c }
      case classExpression: OWLClassExpression =>
        configuration.ontologyReasoner.subsumers(classExpression).collect { case c@Class(_) => c }
  }

  override def Succ(repairType: RepairType, property: OWLObjectProperty, target: IQSaturationNode): collection.Set[OWLClassExpression] = {
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
      Console.err.println("Target node: " + target.toShortDLString())
      Console.err.println("Computed Succ: " + succ.map(_.toShortDLString).mkString("{", ",", "}"))
      Console.err.println("Types: " + types.map(_.toShortDLString).mkString("{", ",", "}"))
      throw RuntimeException() // sanity check, could be removed
    succ
  }

}

class NoSaturation(using configuration: RepairConfiguration) extends Saturation[IQSaturationNode] {

  extension (node: IQSaturationNode) {
    infix def hasType(classExpression: OWLClassExpression)(using configuration: RepairConfiguration): Boolean = {
      node match
        case individualNode: OWLIndividual => configuration.trivialReasoner.types(individualNode) contains classExpression
        case classExpressionNode: OWLClassExpression => configuration.trivialReasoner.subsumers(classExpressionNode) contains classExpression
    }
  }

  override def getSuccessors(node: IQSaturationNode): Iterable[(OWLObjectProperty, IQSaturationNode)] = {
    node match
      case individual: OWLIndividual =>
        configuration.axioms.collect {
          case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject, target) if subject equals individual => (property, target)
          case ClassAssertion(_, ObjectSomeValuesFrom(property@ObjectProperty(_), filler), jndividual) if individual equals jndividual => (property, filler)
        }
      case classExpression: OWLClassExpression =>
        classExpression.topLevelConjuncts().collect {
          case ObjectSomeValuesFrom(property@ObjectProperty(_), filler) => (property, filler)
        }
  }

  override def getLabels(node: IQSaturationNode): Iterable[OWLClass] = {
    node match
      case individual: OWLIndividual =>
        configuration.axioms.collect {
          case ClassAssertion(_, clazz @ Class(_), jndividual) if individual equals jndividual => clazz
        }
      case classExpression: OWLClassExpression =>
        classExpression.topLevelConjuncts().filter(_.isClass).map(_.asOWLClass())
  }

  override def Succ(repairType: RepairType, property: OWLObjectProperty, target: IQSaturationNode): collection.Set[OWLClassExpression] = {
    repairType.atoms.collect {
      case ObjectSomeValuesFrom(qroperty, filler) if (property equals qroperty) && (target hasType filler) => filler
    }
  }

}
