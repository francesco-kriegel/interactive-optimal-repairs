package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*

import de.tu_dresden.inf.lat.interactive_optimal_repairs.Util.Nominal
import org.phenoscape.scowl.*
import org.semanticweb.elk.owlapi.ElkReasonerFactory
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import scala.collection.mutable
import scala.jdk.StreamConverters.*
import scala.jdk.CollectionConverters._

/* This class encapsulates an instance of the ELK reasoner and provides methods with which the reasoning results can be accessed
* in a controlled manner and especially for OWL class expressions that are no named classes.  It currently supports the description
* logic 𝓔𝓛.  While it is expected that the supplied `axioms` are fully compliant with 𝓔𝓛, the access methods also support as further
* class expressions nominals {a} and successors ∃r.{b}, but the subsumers of the latter are determined only partially in a way that
* suffices for the computation of a repair. */
class ELReasoner(axioms: Iterable[OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom],
                 classExpressions: Iterable[OWLClassExpression],
                 allowNewClassExpressions: Boolean = true)
  extends PartialOrdering[OWLClassExpression] {

  private val ontology = OWLManager.createOWLOntologyManager().createOntology()
  private val premises = mutable.HashSet[OWLClassExpression]()
  axioms.foreach(addAxiom)

  private def addAxiom(axiom: OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom): Unit = {
    ontology.addAxiom(axiom)
    if axiom.isInstanceOf[OWLSubClassOfAxiom] then
      premises.add(axiom.asInstanceOf[OWLSubClassOfAxiom].getSubClass)
  }

  def addAxiomAndFlush(axiom: OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom): Unit = {
    addAxiom(axiom)
    elkReasoner.flush()
  }

  private def removeAxiom(axiom: OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom): Unit = {
    ontology.removeAxiom(axiom)
  }

  def removeAxiomAndFlush(axiom: OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom): Unit = {
    removeAxiom(axiom)
    elkReasoner.flush()
  }

  private val representativeOf = mutable.HashMap[OWLClassExpression, OWLClass]()
  private val representativeFor = mutable.HashMap[OWLClass, OWLClassExpression]()

  private val nominals = mutable.HashSet[OWLObjectOneOf]()
  private val successors = mutable.HashSet[OWLObjectSomeValuesFrom]()

  def addRepresentative(classExpression: OWLClassExpression): Unit = {
    if (allowNewClassExpressions)
      _addRepresentative(classExpression)
      elkReasoner.flush()
    else
      throw new RuntimeException("No new class expressions in the reasoner are allowed.")
  }

  private def _addRepresentative(classExpression: OWLClassExpression): Unit = {
    classExpression match
      case nominal@Nominal(_) =>
        nominals += nominal
      case successor@ObjectSomeValuesFrom(_@ObjectProperty(_), nominal@Nominal(_)) =>
        successors += successor
        nominals += nominal
      case _ =>
        val representative =
          classExpression match
            case c @ Class(_) => c
            case _ => Class("internal_representative_class_for#" + classExpression)
        representativeOf(classExpression) = representative
        representativeFor(representative) = classExpression
        if (!(classExpression equals representative))
          ontology.addAxiom(EquivalentClasses(representative, classExpression))
  }

  private def hasRepresentative(classExpression: OWLClassExpression): Boolean = {
    classExpression match
      case nominal@Nominal(_) =>
        nominals contains nominal
      case successor@ObjectSomeValuesFrom(_@ObjectProperty(_), _@Nominal(_)) =>
        successors contains successor
      case _ =>
        representativeOf contains classExpression
  }

  private def ensureHasRepresentative(classExpression: OWLClassExpression): Unit = {
    representativeOf.synchronized {
      if (!hasRepresentative(classExpression))
        addRepresentative(classExpression)
    }
  }

  representativeOf(OWLThing) = OWLThing
  representativeFor(OWLThing) = OWLThing
  classExpressions.foreach(_addRepresentative)

  private val elkReasoner = ElkReasonerFactory().createNonBufferingReasoner(ontology)
  elkReasoner.precomputeInferences()
  elkReasoner.flush()

  def dispose(): Unit = {
    elkReasoner.dispose()
  }

  def entails(axiom: OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom): Boolean = {
    axiom match {
      case subClassOfAxiom: OWLSubClassOfAxiom => isSubsumedBy(subClassOfAxiom.getSubClass, subClassOfAxiom.getSuperClass)
      case classAssertionAxiom: OWLClassAssertionAxiom => isInstanceOf(classAssertionAxiom.getIndividual, classAssertionAxiom.getClassExpression)
      case objectPropertyAssertionAxiom: OWLObjectPropertyAssertionAxiom => elkReasoner.isEntailed(objectPropertyAssertionAxiom)
    }
  }

  def isInstanceOf(individual: OWLIndividual, classExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(classExpression)
    types(individual).contains(classExpression)
  }

  def instances(classExpression: OWLClassExpression): LazyList[OWLNamedIndividual] = {
    classExpression match
      case Nominal(individual) =>
        LazyList(individual)
      case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) =>
        ontology.getABoxAxioms(Imports.INCLUDED).stream().toScala(LazyList).collect {
          case ObjectPropertyAssertion(_, qroperty, subject@NamedIndividual(_), uarget) if (property equals qroperty) && (target equals uarget) => subject
        }
      case _ =>
        elkReasoner.instances(representativeOf(classExpression)).toScala(LazyList)
  }

  def types(individual: OWLIndividual): LazyList[OWLClassExpression] = {
    // TODO: treat anonymous individuals
    (if nominals contains Nominal(individual.asOWLNamedIndividual()) then LazyList(Nominal(individual.asOWLNamedIndividual())) else LazyList.empty) concat
      (successors.filter { case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) => elkReasoner.isEntailed(individual.asOWLNamedIndividual() Fact (property, target)); case _ => false }) concat
      elkReasoner.types(individual.asOWLNamedIndividual()).toScala(LazyList).map(representativeFor)
  }

  def premisesAmongTypes(individual: OWLIndividual): LazyList[OWLClassExpression] = {
    types(individual).filter(premises)
  }

  def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(superClassExpression)
    subsumers(subClassExpression).contains(superClassExpression)
  }

  def subsumers(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    ensureHasRepresentative(classExpression)
    classExpression match
      case Nominal(individual) =>
        types(individual)
      case successor@ObjectSomeValuesFrom(_@ObjectProperty(_), _@Nominal(_)) =>
        instances(successor).flatMap(types) // Not correct in general, but correct in the way it is used during repair construction.
      case _ =>
        java.util.stream.Stream.concat(
          elkReasoner.equivalentClasses(representativeOf(classExpression)),
          elkReasoner.superClasses(representativeOf(classExpression))
        ).toScala(LazyList).map(representativeFor)
  }

  def subsumees(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    ensureHasRepresentative(classExpression)
    classExpression match
      case nominal@Nominal(_) =>
        LazyList(nominal)
      case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) =>
        ontology.getABoxAxioms(Imports.INCLUDED).stream().toScala(LazyList).collect {
          case ObjectPropertyAssertion(_, qroperty, subject@NamedIndividual(_), uarget) if (property equals qroperty) && (target equals uarget) => Nominal(subject)
        }
      case _ =>
        java.util.stream.Stream.concat(
          elkReasoner.equivalentClasses(representativeOf(classExpression)),
          elkReasoner.subClasses(representativeOf(classExpression))
        ).toScala(LazyList).filterNot(_ equals OWLNothing).map(representativeFor)
  }

  def premisesAmongSubsumers(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    subsumers(classExpression).filter(premises)
  }

  def premisesAmongSubsumees(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    subsumees(classExpression).filter(premises)
  }

  override def tryCompare(x: OWLClassExpression, y: OWLClassExpression): Option[Int] = {
    if (lt(x, y))          Some(-1)
    else if (equiv(x, y))  Some(0)
    else if (gt(x, y))     Some(1)
    else                   None
  }

  override def lteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || lt(x, y)

  override def gteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || gt(x, y)

  override def lt(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.superClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

  override def gt(x: OWLClassExpression, y: OWLClassExpression): Boolean = lt(y, x)

  override def equiv(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.equivalentClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

}
