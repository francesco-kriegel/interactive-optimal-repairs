package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.*
import uk.ac.manchester.cs.owl.owlapi.concurrent.ConcurrentOWLOntologyImpl
import uk.ac.manchester.cs.owl.owlapi.{InitVisitorFactory, Internals, MapPointer, OWLAxiomIndexImpl}

import java.lang.reflect.{InvocationTargetException, Method}
import java.util
import java.util.stream.Stream
import javax.annotation.ParametersAreNonnullByDefault
import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*

object Util {

  def maximalElements[T](elements: Iterable[T], lteq: (T,T) => Boolean): Set[T] = {
    elements.foldLeft(Set.empty[T])((maximalElements, element) => {
      if (maximalElements.exists(lteq(element, _)))
        maximalElements
      else
        maximalElements.filterNot(lteq(_, element)) + element
    })
  }

  def minimalElements[T](elements: Iterable[T], lteq: (T,T) => Boolean): Set[T] = {
    maximalElements(elements, (x,y) => lteq(y,x))
  }

  implicit class ImplicitBoolean(b: Boolean) {

    /* The second argument `c` is only evaluated if needed, i.e., if the first argument `b` is true. */
    def implies(c: => Boolean): Boolean = !b || c

  }

  class OWLSubClassOfAxiomReasonerRequest(subClassOfAxiom: OWLSubClassOfAxiom) {

    def wrt(classification: ExtendedClassification): Boolean =
      classification entails subClassOfAxiom

  }

  implicit class ImplicitOWLClassExpression(classExpression: OWLClassExpression) {

    lazy val isAtom: Boolean =
      classExpression match
        case c @ Class(_) => !(c equals OWLThing)
        case ObjectSomeValuesFrom(_, _) => true
        case ObjectHasValue(_, _@NamedIndividual(_)) => true
        case ObjectOneOf(individuals) if (individuals.size == 1) && individuals.head.isNamed => true
        case _ => false

    lazy val isClass: Boolean =
      classExpression match
        case c@Class(_) => !(c equals OWLThing)
        case _ => false

    lazy val isObjectSomeValuesFrom: Boolean =
      classExpression match
        case ObjectSomeValuesFrom(_, _) => true
        case _ => false

    def topLevelConjuncts(): LazyList[OWLClassExpression] =
      classExpression.conjunctSet().toScala(LazyList).filter(_.isAtom)

    def getTopLevelConjuncts: collection.Set[OWLClassExpression] =
      classExpression.asConjunctSet().asScala.filter(_.isAtom)

    def isSubsumedBy(other: OWLClassExpression): OWLSubClassOfAxiomReasonerRequest =
      OWLSubClassOfAxiomReasonerRequest(classExpression SubClassOf other)

    def subsumes(other: OWLClassExpression): OWLSubClassOfAxiomReasonerRequest =
      OWLSubClassOfAxiomReasonerRequest(other SubClassOf classExpression)

    def isCoveredBy(others: Iterable[OWLClassExpression]): CoverageReasonerRequest =
      CoverageReasonerRequest(Set(classExpression), others, false)

    def isCoveredBy(others: RepairType): CoverageReasonerRequest =
      CoverageReasonerRequest(Set(classExpression), others.atoms, false)

    def isStrictlyCoveredBy(others: Iterable[OWLClassExpression]): CoverageReasonerRequest =
      CoverageReasonerRequest(Set(classExpression), others, true)

    def isStrictlyCoveredBy(others: RepairType): CoverageReasonerRequest =
      CoverageReasonerRequest(Set(classExpression), others.atoms, true)

    lazy val reduced: OWLClassExpression = {
      given ontologyManager: OWLOntologyManager = OWLManager.createOWLOntologyManager() // TODO
      val classificationOfEmptyOntology = ExtendedClassification(Set.empty, classExpression.getNestedClassExpressions.asScala, true)
      val reduction =
        if (classExpression subsumes OWLThing wrt classificationOfEmptyOntology)
          OWLThing
        else
          minimalElements(
            classExpression.topLevelConjuncts().map {
              case ObjectSomeValuesFrom(property, filler) => property some filler.reduced
              case c @ Class(_)                           => c
            },
            classificationOfEmptyOntology.lteq
          ) reduceLeft { _ and _ }
      classificationOfEmptyOntology.dispose()
      reduction
    }

    lazy val toDLString: String =
      classExpression match
        case OWLThing =>
          "⊤"
        case Class(iri) =>
          iri.toString
        case ObjectOneOf(is) if is.size == 1 =>
          "{" + is.head.toDLString + "}"
        case ObjectSomeValuesFrom(property@ObjectProperty(iri), filler) =>
          "∃" + iri.toString + "." + filler.toDLString
        case ObjectIntersectionOf(operands) =>
          if (operands.isEmpty)
            "⊤"
          else if (operands.size == 1)
            operands.head.toDLString
          else
            "(" + operands.head.toDLString + operands.tail.foldLeft("")((str, op) => str + "⊓" + op.toDLString) + ")"
        case _ =>
          throw new IllegalArgumentException("Only 𝓔𝓛 concepts are supported.")


    lazy val toShortDLString: String =
      classExpression match
        case OWLThing =>
          "⊤"
        case Class(iri) =>
          iri.getShortForm
        case ObjectOneOf(is) if is.size == 1 =>
          "{" + is.head.toShortDLString + "}"
        case ObjectSomeValuesFrom(property@ObjectProperty(iri), filler) =>
          "∃" + iri.getShortForm + "." + filler.toShortDLString
        case ObjectIntersectionOf(operands) =>
          if (operands.isEmpty)
            "⊤"
          else if (operands.size == 1)
            operands.head.toShortDLString
          else
            "(" + operands.head.toShortDLString + operands.tail.foldLeft("")((str, op) => str + "⊓" + op.toShortDLString) + ")"
        case _ =>
          throw new IllegalArgumentException("Only 𝓔𝓛 concepts are supported.")
  }

  implicit class ImplicitOWLSubClassOfAxiom(subClassOfAxiom: OWLSubClassOfAxiom) {

    def isEntailedBy(classification: ExtendedClassification): Boolean =
      classification entails subClassOfAxiom

    lazy val toDLString: String =
      subClassOfAxiom.getSubClass.toDLString + " ⊑ " + subClassOfAxiom.getSuperClass.toDLString

    lazy val toShortDLString: String =
      subClassOfAxiom.getSubClass.toShortDLString + " ⊑ " + subClassOfAxiom.getSuperClass.toShortDLString

  }

  implicit class ImplicitOWLClassAssertionAxiom(classAssertion: OWLClassAssertionAxiom) {

    def isEntailedBy(classification: ExtendedClassification): Boolean =
      classification entails classAssertion

    lazy val toDLString: String =
      classAssertion.getIndividual.toDLString + " : " + classAssertion.getClassExpression.toDLString

    lazy val toShortDLString: String =
      classAssertion.getIndividual.toShortDLString + " : " + classAssertion.getClassExpression.toShortDLString

  }

  implicit class ImplicitOWLIndividual(individual: OWLIndividual) {

    lazy val toDLString: String =
      individual match {
        case NamedIndividual(iri) => iri.toString
        case AnonymousIndividual(id) => id
      }

    lazy val toShortDLString: String =
      individual match {
        case NamedIndividual(iri) => iri.getShortForm
        case AnonymousIndividual(id) => id
      }

  }

  implicit class ImplicitOWLObjectPropertyAssertionAxiom(propertyAssertion: OWLObjectPropertyAssertionAxiom) {

    def isEntailedBy(classification: ExtendedClassification): Boolean =
      classification entails propertyAssertion

    lazy val toDLString: String =
      propertyAssertion.getSubject.toDLString + " " + propertyAssertion.getProperty.toDLString + " " + propertyAssertion.getObject.toDLString

    lazy val toShortDLString: String =
      propertyAssertion.getSubject.toShortDLString + " " + propertyAssertion.getProperty.toShortDLString + " " + propertyAssertion.getObject.toShortDLString

  }

  implicit class ImplicitOWLObjectPropertyExpression(propertyExpression: OWLObjectPropertyExpression) {

    lazy val toDLString: String =
      propertyExpression match {
        case ObjectProperty(iri) => iri.toString
        case _ => ???
      }

    lazy val toShortDLString: String =
      propertyExpression match {
        case ObjectProperty(iri) => iri.getShortForm
        case _ => ???
      }

  }

  implicit class ImplicitIterableOfOWLClassExpressions(classExpressions: Iterable[OWLClassExpression]) {

    def isCoveredBy(others: Iterable[OWLClassExpression]): CoverageReasonerRequest =
      CoverageReasonerRequest(classExpressions, others, false)

    def isCoveredBy(others: RepairType): CoverageReasonerRequest =
      CoverageReasonerRequest(classExpressions, others.atoms, false)

    def isStrictlyCoveredBy(others: Iterable[OWLClassExpression]): CoverageReasonerRequest =
      CoverageReasonerRequest(classExpressions, others, true)

    def isStrictlyCoveredBy(others: RepairType): CoverageReasonerRequest =
      CoverageReasonerRequest(classExpressions, others.atoms, true)

  }

  class CoverageReasonerRequest(classExpressions: Iterable[OWLClassExpression], others: Iterable[OWLClassExpression], strict: Boolean) {

    def wrt(classification: ExtendedClassification): Boolean =
      classExpressions.forall(c => others.exists(d => c isSubsumedBy d wrt classification))
        && (strict implies !others.forall(c => classExpressions.exists(d => c isSubsumedBy d wrt classification)))

  }


  object Nominal {

    def apply(individual: OWLNamedIndividual): OWLObjectOneOf =
      ObjectOneOf(individual)

    def unapply(expression: OWLObjectOneOf): Option[OWLNamedIndividual] =
      val individuals = expression.getIndividuals.asScala.toSet
      if individuals.size == 1 && individuals.head.isNamed then
        Some(individuals.head.asOWLNamedIndividual())
      else
        None

  }

  /**
   * A class that encapsulates an instance of {@link org.semanticweb.owlapi.model.OWLOntology} and adds a further index
   * mapping each instance of {@link org.semanticweb.owlapi.model.OWLIndividual} to the set of all instances of
   * {@link org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom} in which it occurs in object position.
   */
  object AdditionallyIndexedOWLOntology {
    /* Creating a new visitor that is not defined in uk.ac.manchester.cs.owl.owlapi.InitVisitorFactory */
    private val INDIVIDUALSUPERNAMED = new AdditionallyIndexedOWLOntology.ConfigurableInitIndividualVisitor[OWLIndividual](false, true)

    private class ConfigurableInitIndividualVisitor[K <: OWLObject](private val sub: Boolean, named: Boolean)
      extends InitVisitorFactory.InitIndividualVisitor[K](sub, named) {
      @SuppressWarnings(Array("unchecked"))
      @ParametersAreNonnullByDefault
      override def visit(axiom: OWLNegativeObjectPropertyAssertionAxiom): K =
        if sub then axiom.getSubject.asInstanceOf[K] else axiom.getObject.asInstanceOf[K]

      @SuppressWarnings(Array("unchecked"))
      @ParametersAreNonnullByDefault
      override def visit(axiom: OWLNegativeDataPropertyAssertionAxiom): K =
        if sub then axiom.getSubject.asInstanceOf[K] else axiom.getObject.asInstanceOf[K]

      @SuppressWarnings(Array("unchecked"))
      @ParametersAreNonnullByDefault
      override def visit(axiom: OWLObjectPropertyAssertionAxiom): K =
        if sub then axiom.getSubject.asInstanceOf[K] else axiom.getObject.asInstanceOf[K]

      @SuppressWarnings(Array("unchecked"))
      @ParametersAreNonnullByDefault
      override def visit(axiom: OWLDataPropertyAssertionAxiom): K =
        if sub then axiom.getSubject.asInstanceOf[K] else axiom.getObject.asInstanceOf[K]
    }
  }

  final class AdditionallyIndexedOWLOntology(private val ontology: OWLOntology) {

    @transient private val objectPropertyAssertionsByObjectIndividual: MapPointer[OWLIndividual, OWLObjectPropertyAssertionAxiom] = {
      try {
        val intsField = classOf[OWLAxiomIndexImpl].getDeclaredField("ints")
        intsField.setAccessible(true)
        val ints =
          if ontology.isInstanceOf[ConcurrentOWLOntologyImpl] then
            val delegateField = classOf[ConcurrentOWLOntologyImpl].getDeclaredField("delegate")
            delegateField.setAccessible(true)
            intsField.get(delegateField.get(ontology).asInstanceOf[OWLOntology]).asInstanceOf[Internals]
          else
            intsField.get(ontology).asInstanceOf[Internals]
        val buildLazyMethod = util.Arrays.stream(classOf[Internals].getDeclaredMethods).filter((method: Method) => method.getName == "buildLazy").findAny.get
        buildLazyMethod.setAccessible(true)
        buildLazyMethod.invoke(ints, AxiomType.OBJECT_PROPERTY_ASSERTION, AdditionallyIndexedOWLOntology.INDIVIDUALSUPERNAMED).asInstanceOf[MapPointer[OWLIndividual, OWLObjectPropertyAssertionAxiom]]
      } catch {
        case e@(_: NoSuchFieldException | _: IllegalAccessException | _: InvocationTargetException) =>
          throw RuntimeException(e)
      }
    }: @SuppressWarnings(Array("unchecked"))

    ontology.getOWLOntologyManager.addOntologyChangeListener(
      _.stream.forEach((change: OWLOntologyChange) => {
        if change.isAxiomChange(AxiomType.OBJECT_PROPERTY_ASSERTION) then
          if change.isAddAxiom then
            val axiom = change.getAddedAxiom.get.asInstanceOf[OWLObjectPropertyAssertionAxiom]
            objectPropertyAssertionsByObjectIndividual.put(axiom.getObject, axiom)
          else if change.isRemoveAxiom then
            val axiom = change.getRemovedAxiom.get.asInstanceOf[OWLObjectPropertyAssertionAxiom]
            objectPropertyAssertionsByObjectIndividual.remove(axiom.getObject, axiom)
      }),
      new SpecificOntologyChangeBroadcastStrategy(ontology)
    )

    def objectPropertyAssertionAxiomsWithSubject(individual: OWLIndividual): Stream[OWLObjectPropertyAssertionAxiom] = {
      /* The OWLAPI already manages an index for the desired results, so there is no need to create a second one. */
      ontology.getObjectPropertyAssertionAxioms(individual).stream()
    }

    def objectPropertyAssertionAxiomsWithObject(individual: OWLIndividual): Stream[OWLObjectPropertyAssertionAxiom] = {
      objectPropertyAssertionsByObjectIndividual.getValues(individual).stream()
    }

    def getObjectPropertyAssertionAxiomsWithObject(individual: OWLIndividual): collection.Set[OWLObjectPropertyAssertionAxiom] = {
      objectPropertyAssertionsByObjectIndividual.getValues(individual).asScala.toSet
    }

  }

}
