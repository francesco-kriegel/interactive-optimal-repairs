package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.vocab.OWLRDFVocabulary

import scala.jdk.StreamConverters.*

/**
 * Used to check whether an ontology is fully supported, i.e., does not contain language constructs which cannot be
 * handled by our repair approach and its implementation.
 */
object ELExpressivityChecker {

  def check(ontology: OWLOntology): Boolean = {
    ontology.axioms(Imports.INCLUDED).toScala(LazyList).forall(checkAxiom)
  }

  def checkAxiom(axiom: OWLAxiom): Boolean = {
    axiom match
      case Declaration(annotations, entity) =>
        annotations.forall(checkAnnotation)
      case SubClassOf(annotations, subClass, superClass) =>
        annotations.forall(checkAnnotation)
          && checkClassExpression(subClass)
          && checkClassExpression(superClass)
      case EquivalentClasses(annotations, operands) =>
        annotations.forall(checkAnnotation)
          && operands.forall(checkClassExpression)
      case ObjectPropertyDomain(annotations, property, filler) =>
        annotations.forall(checkAnnotation)
          && checkObjectPropertyExpression(property)
          && checkClassExpression(filler)
      case ClassAssertion(annotations, classExpression, individual) =>
        annotations.forall(checkAnnotation)
          && checkClassExpression(classExpression)
      case ObjectPropertyAssertion(annotations, property, subject, target) =>
        annotations.forall(checkAnnotation)
          && checkObjectPropertyExpression(property)
      case _: OWLAnnotationAxiom =>
        true
      case _ =>
        false
  }

  def checkClassExpression(concept: OWLClassExpression): Boolean = {
    concept match
      case c @ Class(_) =>
        !(c equals OWLNothing)
      case ObjectIntersectionOf(operands) =>
        operands.forall(checkClassExpression)
      case ObjectSomeValuesFrom(property, filler) =>
        checkObjectPropertyExpression(property)
          && checkClassExpression(filler)
      case ObjectMinCardinality(num, property, filler) =>
        (num equals 0)
          || ((num equals 1)
               && checkObjectPropertyExpression(property)
               && checkClassExpression(filler))
      case _ =>
        false
  }

  def checkObjectPropertyExpression(property: OWLObjectPropertyExpression): Boolean = {
    property match
      case r @ ObjectProperty(_) =>
        !(r equals OWLRDFVocabulary.OWL_TOP_OBJECT_PROPERTY)
          && !(r equals OWLRDFVocabulary.OWL_BOTTOM_OBJECT_PROPERTY)
      case _ =>
        false
  }

  def checkAnnotation(annotation: OWLAnnotation): Boolean = {
    true
  }

  def normalizeClassExpression(classExpression: OWLClassExpression): OWLClassExpression = {
    classExpression match
      case c @ Class(_) => c
      case ObjectIntersectionOf(operands) =>
        if (operands.isEmpty) OWLThing
        else operands.map(normalizeClassExpression).reduceLeft(_ and _)
      case ObjectSomeValuesFrom(property, filler) =>
        property some normalizeClassExpression(filler)
      case ObjectMinCardinality(num, property, filler) if num equals 0 =>
        OWLThing
      case ObjectMinCardinality(num, property, filler) if num equals 1 =>
        property some normalizeClassExpression(filler)
      case _ =>
        throw new IllegalArgumentException("Only 𝓔𝓛 concepts are supported.")
  }

  def getELAxioms(ontology: OWLOntology): LazyList[OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom] = {
    ontology.axioms(Imports.INCLUDED).toScala(LazyList).filter(checkAxiom)
      .flatMap[OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom] {
        case SubClassOf(_, subClass, superClass) =>
          Set(normalizeClassExpression(subClass) SubClassOf normalizeClassExpression(superClass))
        case EquivalentClasses(_, operands) =>
          for (subClass <- operands; superClass <- operands if !(subClass equals superClass))
            yield normalizeClassExpression(subClass) SubClassOf normalizeClassExpression(superClass)
        case ObjectPropertyDomain(_, property, filler) =>
          Set((property some OWLThing) SubClassOf normalizeClassExpression(filler))
        case ClassAssertion(annotations, classExpression, individual) =>
          Set(individual Type normalizeClassExpression(classExpression))
        case ObjectPropertyAssertion(annotations, property, subject, target) =>
          Set(subject Fact (property, target))
        case _ =>
          Set.empty[OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom]
      }
  }

  def getELFragment(ontology: OWLOntology): LazyList[OWLAxiom] = {
    ontology.axioms(Imports.INCLUDED).toScala(LazyList).filter(checkAxiom)
//      .flatMap {
//        case SubClassOf(annotations, subClass, superClass) =>
//          Set(SubClassOf(annotations, normalizeClassExpression(subClass), normalizeClassExpression(superClass)))
//        case EquivalentClasses(annotations, operands) =>
//          for (subClass <- operands; superClass <- operands if !(subClass equals superClass))
//            yield SubClassOf(annotations, normalizeClassExpression(subClass), normalizeClassExpression(superClass))
//        case ObjectPropertyDomain(annotations, property, filler) =>
//          Set(SubClassOf(annotations, (property some OWLThing), normalizeClassExpression(filler)))
//        case ClassAssertion(annotations, classExpression, individual) =>
//          Set(ClassAssertion(annotations, normalizeClassExpression(classExpression), individual))
////        case ObjectPropertyAssertion(annotations, property, subject, target) =>
////          Set(ObjectPropertyAssertion(annotations, property, subject, target))
//        case ax =>
//          Set(ax)
//      }
  }

}