package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*

class RepairRequest(val axioms: collection.Set[Query]) {

  def this(axioms: Query*) = this(axioms.toSet)

  def getClassExpressions(individual: OWLNamedIndividual): Set[OWLClassExpression] = {
    axioms.collect({
      case ClassAssertion(annotations, classExpression, jndividual)
        if individual == jndividual => classExpression
    }).toSet
  }

}
