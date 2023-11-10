package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*

import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLClassExpression, OWLObjectPropertyAssertionAxiom, OWLSubClassOfAxiom}

import scala.jdk.StreamConverters.*

class RepairConfiguration(val axioms: collection.Set[OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom], val repairRequest: RepairRequest) {

  val subClassExpressions: collection.Set[OWLClassExpression] =
    axioms.flatMap(_.nestedClassExpressions().toScala(LazyList)) concat
      repairRequest.axioms.flatMap(_.nestedClassExpressions().toScala(LazyList)) // concat
      // repairRequest.axioms.collect {
      //   case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
      //     collection.Set(oneOf(target), property some oneOf(target))
      // }.flatten

  val trivialReasoner: ELReasoner = ELReasoner(Set.empty, subClassExpressions, true)
  val ontologyReasoner: ELReasoner = ELReasoner(axioms, subClassExpressions, true)

}
