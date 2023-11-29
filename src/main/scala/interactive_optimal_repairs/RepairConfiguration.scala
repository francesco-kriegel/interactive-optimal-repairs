package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLOntology, OWLOntologyManager, OWLSubClassOfAxiom}

import scala.collection.mutable
import scala.jdk.CollectionConverters.*

class RepairConfiguration(val ontology: OWLOntology, val request: RepairRequest)(using ontologyManager: OWLOntologyManager) {

  println("Initializing repair configuration with " + ontology.getAxioms(Imports.INCLUDED).size() + " axioms in the ontology and " + request.axioms.size + " queries in the repair request ...")

  private val _subClassExpressions: collection.Set[OWLClassExpression] =
    ontology.getNestedClassExpressions.asScala union
      request.axioms.flatMap(_.getNestedClassExpressions.asScala)

  val subClassExpressions =
    _subClassExpressions union
      _subClassExpressions.collect { case ObjectSomeValuesFrom(property, filler) if !(filler equals OWLThing) => property some OWLThing }

  println("There are " + subClassExpressions.size + " subclass expressions.")

  val conceptInclusions =
    ontology.getTBoxAxioms(Imports.INCLUDED).asScala.flatMap {
      case axiom@SubClassOf(_, _, _) => Iterable.single(axiom)
      case _@EquivalentClasses(_, operands) if operands.size > 1 =>
        val axioms = mutable.HashSet[OWLSubClassOfAxiom]()
        val it = operands.iterator
        var current = it.next()
        val first = current
        while it.hasNext do
          val next = it.next()
          axioms += current SubClassOf next
          current = next
        axioms += current SubClassOf first
        axioms
      case _ => Iterable.empty
    }

  val conceptInclusionsMap = mutable.HashMap[OWLClassExpression, mutable.HashSet[OWLClassExpression]]()
  conceptInclusions foreach {
    case SubClassOf(_, premise, conclusion) =>
      conceptInclusionsMap.getOrElseUpdate(premise, { mutable.HashSet[OWLClassExpression]() }).add(conclusion)
  }
  
  val trivialReasoner: ELReasoner = ELReasoner(Set.empty, subClassExpressions, true)
  val ontologyReasoner: ELReasoner = ELReasoner(ontology, subClassExpressions, true)

  def dispose(): Unit = {
    trivialReasoner.dispose()
    ontologyReasoner.dispose()
  }

}
