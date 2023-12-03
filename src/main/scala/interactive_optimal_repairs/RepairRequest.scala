package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*

class RepairRequest(val negativeAxioms: collection.Set[Query], val positiveAxioms: collection.Set[Query]) {

  def getNegativeClassExpressions(individual: OWLNamedIndividual): Set[OWLClassExpression] = {
    negativeAxioms.collect({
      case ClassAssertion(annotations, classExpression, jndividual)
        if individual == jndividual => classExpression
    }).toSet
  }

}
