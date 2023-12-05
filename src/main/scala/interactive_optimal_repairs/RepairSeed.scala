package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Util.{ImplicitOWLClassExpression, maximalElements}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLClassExpression, OWLNamedIndividual}

import scala.collection.mutable

class RepairSeed(protected[interactive_optimal_repairs] val preprocessed: Boolean = false, protected[interactive_optimal_repairs] val axioms: Iterable[OWLClassAssertionAxiom])(using configuration: RepairConfiguration) {

  def this(preprocessed: Boolean, axioms: OWLClassAssertionAxiom*)(using configuration: RepairConfiguration) = this(preprocessed, axioms.toSet)

  private val repairTypes = mutable.HashMap[OWLNamedIndividual, RepairType]()

  def apply(individual: OWLNamedIndividual): RepairType = getRepairType(individual)

  def getRepairType(individual: OWLNamedIndividual): RepairType = {
    repairTypes.getOrElseUpdate(individual, {
      if preprocessed
      then RepairType(KernelObject(individual), getClassExpressions(individual))
      else
        val atoms =
          maximalElements(
            (getClassExpressions(individual) intersect configuration.classificationOfInputOntology.types(individual).toSet)
              .filter(_.isAtom),
            _ isSubsumedBy _ wrt configuration.classificationOfEmptyOntology)
        val repairType = RepairType(KernelObject(individual), atoms)
        if !repairType.isRepairType then throw RuntimeException("The provided axioms do not uniquely determine a repair seed.  Please check the code that instantiates this repair seed.")
        repairType
    })
  }

  private def getClassExpressions(individual: OWLNamedIndividual): Set[OWLClassExpression] = {
    axioms.collect({
      case ClassAssertion(annotations, classExpression, jndividual) if individual == jndividual => classExpression
    }).toSet
  }

}
