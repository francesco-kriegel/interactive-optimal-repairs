package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.semanticweb.elk.owlapi.ElkReasoner
import org.semanticweb.owlapi.model
import org.semanticweb.owlapi.model.{OWLAxiom, OWLClass, OWLClassExpression, OWLIndividual, OWLNamedIndividual, OWLObject, OWLOntology}
import org.semanticweb.owlapi.model.parameters.{ChangeApplied, Imports}

// Allows for code that looks like written for OWLAPI5
object OWLAPI5CodeConversion {

  extension(ontology: OWLOntology) {

    def axioms(includeImportsClosure: Imports): java.util.stream.Stream[OWLAxiom] = {
      ontology.getAxioms(includeImportsClosure).stream()
    }

    def addAxiom(axiom: OWLAxiom): ChangeApplied = {
      ontology.getOWLOntologyManager.addAxiom(ontology, axiom)
    }

    def removeAxiom(axiom: OWLAxiom): ChangeApplied = {
      ontology.getOWLOntologyManager.removeAxiom(ontology, axiom)
    }

    def individualsInSignature(includeImportsClosure: Imports): java.util.stream.Stream[OWLNamedIndividual] = {
      ontology.getIndividualsInSignature(includeImportsClosure).stream()
    }

  }

  extension[T <: OWLObject](owlObject: T) {

    def nestedClassExpressions(): java.util.stream.Stream[OWLClassExpression] = {
      owlObject.getNestedClassExpressions.stream()
    }

  }

  extension(classExpression: OWLClassExpression) {

    def conjunctSet(): java.util.stream.Stream[OWLClassExpression] = {
      classExpression.asConjunctSet().stream()
    }

  }

  extension(reasoner: ElkReasoner) {

    def instances(classExpression: OWLClassExpression): java.util.stream.Stream[OWLNamedIndividual] = {
      reasoner.getInstances(classExpression, false).getFlattened.stream()
    }

    def types(individual: OWLNamedIndividual): java.util.stream.Stream[OWLClass] = {
      reasoner.getTypes(individual, false).getFlattened.stream()
    }

    def equivalentClasses(classExpression: OWLClassExpression): java.util.stream.Stream[OWLClass] = {
      reasoner.getEquivalentClasses(classExpression).getEntities.stream()
    }

    def subClasses(classExpression: OWLClassExpression): java.util.stream.Stream[OWLClass] = {
      reasoner.getSubClasses(classExpression, false).getFlattened.stream()
    }

    def superClasses(classExpression: OWLClassExpression): java.util.stream.Stream[OWLClass] = {
      reasoner.getSuperClasses(classExpression, false).getFlattened.stream()
    }

  }

}
