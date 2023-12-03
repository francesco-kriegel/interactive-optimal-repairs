package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLOntology, OWLOntologyManager, OWLSubClassOfAxiom}

import scala.collection.mutable
import scala.jdk.CollectionConverters.*

protected class RepairConfiguration(val ontology: OWLOntology,
                                    val request: RepairRequest,
                                    val ontologyReasoner: ExtendedClassificationForMultipleABoxesWithSharedTBox)
                                   (using ontologyManager: OWLOntologyManager) {

  def this(ontology: OWLOntology, request: RepairRequest)(using ontologyManager: OWLOntologyManager) = {
    this(ontology, request, ExtendedClassificationForMultipleABoxesWithSharedTBox(ontology, Set.empty, true))
  }

//  println("Initializing repair configuration with " + ontology.getAxioms(Imports.INCLUDED).size() + " axioms in the ontology and " + request.negativeAxioms.size + " queries in the repair request ...")

  private val _subClassExpressions =
    ontology.getNestedClassExpressions.asScala union
      request.negativeAxioms.flatMap(_.getNestedClassExpressions.asScala)

  val subClassExpressions: collection.Set[OWLClassExpression] =
    _subClassExpressions union
      _subClassExpressions.collect { case ObjectSomeValuesFrom(property, filler) if !(filler equals OWLThing) => property some OWLThing }

//  println("There are " + subClassExpressions.size + " subclass expressions.")

  val conceptInclusions: mutable.Set[OWLSubClassOfAxiom] =
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

  val conceptInclusionsMap: mutable.HashMap[OWLClassExpression, mutable.HashSet[OWLClassExpression]] = mutable.HashMap[OWLClassExpression, mutable.HashSet[OWLClassExpression]]()
  conceptInclusions foreach {
    case SubClassOf(_, premise, conclusion) =>
      conceptInclusionsMap.getOrElseUpdate(premise, { mutable.HashSet[OWLClassExpression]() }).add(conclusion)
  }

  val trivialReasoner: ExtendedClassification = ExtendedClassification(Set.empty, subClassExpressions, true)
//  // TODO: Implement a variant of ELReasoner that supports multiple ABoxes with a shared TBox.
//  val ontologyReasoner = ExtendedClassificationForMultipleABoxesWithSharedTBox(ontology, subClassExpressions, true)
  ontologyReasoner.addClassExpressions(subClassExpressions)
  ontologyReasoner.precomputeInferences()

  lazy val iqSaturation: IQSaturation = { given configuration: RepairConfiguration = this; IQSaturation() }

  def dispose(): Unit = {
    trivialReasoner.dispose()
    ontologyReasoner.dispose()
    conceptInclusionsMap.clear()
    conceptInclusions.clear()
  }

}
