package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*
import interactive_optimal_repairs.Util.Nominal

import org.phenoscape.scowl.*
import org.semanticweb.elk.owlapi.ElkReasonerFactory
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.reasoner.InferenceType

import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*

type ELAxiom = OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom

object ELReasoner {

  /* Global selection of the reasoner version */
  private val DefaultImplementation = IndexedELReasoner

  def apply(ontology: OWLOntology,
            classExpressions: collection.Set[OWLClassExpression],
            allowNewClassExpressions: Boolean = true)
           (using ontologyManager: OWLOntologyManager): ELReasoner = {
    //val ontologySolelyForReasoner = ontologyManager.copyOntology(ontology, OntologyCopy.DEEP)
    val ontologySolelyForReasoner = ontologyManager.createOntology(ontology.getAxioms)
//    //TODO: For general use, handle cases where `ontology` is not managed by `ontologyManager`
//    val ontologySolelyForReasoner = ontologyManager.createOntology()
//    ontologyManager.applyChange(
//      AddImport(
//        ontologySolelyForReasoner,
//        ontologyManager.getOWLDataFactory.getOWLImportsDeclaration(ontologyManager.getOntologyDocumentIRI(ontology))
//      )
//    )
//    //ontologyManager.loadOntology(ontologyManager.getOntologyDocumentIRI(ontology))
    DefaultImplementation(ontologySolelyForReasoner, classExpressions, allowNewClassExpressions, () => { ontologyManager.removeOntology(ontologySolelyForReasoner) })
  }

  def apply(axioms: collection.Set[_ <: OWLAxiom], // ELAxiom
            classExpressions: collection.Set[OWLClassExpression],
            allowNewClassExpressions: Boolean)
           (using ontologyManager: OWLOntologyManager): ELReasoner = {
    val ontologySolelyForReasoner = ontologyManager.createOntology(axioms.asInstanceOf[collection.Set[OWLAxiom]].asJava)
    DefaultImplementation(ontologySolelyForReasoner, classExpressions, allowNewClassExpressions, () => { ontologyManager.removeOntology(ontologySolelyForReasoner) })
  }

}

protected trait ELReasoner(ontology: OWLOntology, // axioms: Iterable[ELAxiom],
                 classExpressions: collection.Set[OWLClassExpression],
                 allowNewClassExpressions: Boolean = true,
                 onDisposal: () => Unit = () => {})
  extends PartialOrdering[OWLClassExpression] {

  protected def addAxiom(axiom: ELAxiom): Unit = {
    ontology.addAxiom(axiom)
  }

  def addAxiomAndFlush(axiom: ELAxiom): Unit = {
    addAxiom(axiom)
    elkReasoner.flush()
  }

  protected def removeAxiom(axiom: ELAxiom): Unit = {
    ontology.removeAxiom(axiom)
  }

  def removeAxiomAndFlush(axiom: ELAxiom): Unit = {
    removeAxiom(axiom)
    elkReasoner.flush()
  }

  print(" 1 ")
  protected val elkReasoner = ElkReasonerFactory().createReasoner(ontology)
  print(" 2 ")
  // elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
  print(" 3 ")

  def dispose(): Unit = {
    elkReasoner.dispose()
    onDisposal()
  }

  def addClassExpression(classExpression: OWLClassExpression): Unit

  def entails(axiom: ELAxiom): Boolean
  def isInstanceOf(individual: OWLIndividual, classExpression: OWLClassExpression): Boolean
  def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean

  def types(individual: OWLIndividual): Iterable[OWLClassExpression]
  def instances(classExpression: OWLClassExpression): Iterable[OWLNamedIndividual]
  def subsumers(classExpression: OWLClassExpression): Iterable[OWLClassExpression]
  def subsumees(classExpression: OWLClassExpression): Iterable[OWLClassExpression]

//  def getTypes(individual: OWLIndividual): collection.Set[OWLClassExpression] = types(individual).toSet
//  def getInstances(classExpression: OWLClassExpression): collection.Set[OWLNamedIndividual] = instances(classExpression).toSet
//  def getSubsumers(classExpression: OWLClassExpression): collection.Set[OWLClassExpression] = subsumers(classExpression).toSet
//  def getSubsumees(classExpression: OWLClassExpression): collection.Set[OWLClassExpression] = subsumees(classExpression).toSet

  override def tryCompare(x: OWLClassExpression, y: OWLClassExpression): Option[Int] = {
    if (lt(x, y)) Some(-1)
    else if (equiv(x, y)) Some(0)
    else if (gt(x, y)) Some(1)
    else None
  }

  override def lteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || lt(x, y)

  override def gteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || gt(x, y)

  override def gt(x: OWLClassExpression, y: OWLClassExpression): Boolean = lt(y, x)

}

/* This class encapsulates an instance of the ELK reasoner and provides methods with which the reasoning results can be accessed
* in a controlled manner and especially for OWL class expressions that are no named classes.  It currently supports the description
* logic 𝓔𝓛.  While it is expected that the supplied `axioms` are fully compliant with 𝓔𝓛, the access methods also support as further
* class expressions nominals {a} and successors ∃r.{b}, but the subsumers of the latter are determined only partially in a way that
* suffices for the computation of a repair. */
protected class IndexedELReasoner(ontology: OWLOntology, // axioms: Iterable[ELAxiom],
                                  classExpressions: collection.Set[OWLClassExpression],
                                  allowNewClassExpressions: Boolean = true,
                                  onDisposal: () => Unit = () => {})
  extends ELReasoner(ontology, classExpressions, allowNewClassExpressions, onDisposal) {

  private val _representativeOf = mutable.HashMap[OWLClassExpression, OWLClass]() // java.util.HashMap[OWLClassExpression, OWLClass]().asScala
  private val representativeFor = mutable.HashMap[OWLClass, OWLClassExpression]() // java.util.HashMap[OWLClass, OWLClassExpression]().asScala

  private def representativeOf(classExpression: OWLClassExpression): OWLClass = {
    classExpression match
      case c@Class(_) => c
      case _ => _representativeOf(classExpression)
  }

  protected val nominals = mutable.HashSet[OWLObjectOneOf]() // java.util.HashSet[OWLObjectOneOf]().asScala
  protected val successors = mutable.HashSet[OWLObjectSomeValuesFrom]() // java.util.HashSet[OWLObjectSomeValuesFrom]().asScala

  override def addClassExpression(classExpression: OWLClassExpression): Unit = addRepresentative(classExpression)

  override def dispose(): Unit = {
    super.dispose()
    _representativeOf.clear()
    representativeFor.clear()
    nominals.clear()
    successors.clear()
  }

  private def addRepresentative(classExpression: OWLClassExpression): Unit = {
    if (allowNewClassExpressions)
      addRepresentativeUnchecked(classExpression)
      elkReasoner.flush()
    else
      throw new RuntimeException("No new class expressions in the reasoner are allowed.")
  }

  private def addRepresentativeUnchecked(classExpression: OWLClassExpression): Unit = {
    classExpression match
      case nominal@Nominal(_) =>
        nominals += nominal
      case successor@ObjectSomeValuesFrom(_@ObjectProperty(_), nominal@Nominal(_)) =>
        successors += successor
        nominals += nominal
      //      case _ =>
      //        val representative =
      //          classExpression match
      //            case c @ Class(_) => c
      //            case _ => Class("internal_representative_class_for#" + classExpression)
      //        representativeOf(classExpression) = representative
      //        representativeFor(representative) = classExpression
      //        if (!(classExpression equals representative))
      //          ontology.addAxiom(EquivalentClasses(representative, classExpression))
      case c@Class(_) =>
        // representativeOf(c) = c
        representativeFor(c) = c
      case _ =>
        val representative = Class("internal_representative_class_for#" + classExpression)
        _representativeOf(classExpression) = representative
        representativeFor(representative) = classExpression
        ontology.addAxiom(representative EquivalentTo classExpression)
  }

  private def hasRepresentative(classExpression: OWLClassExpression): Boolean = {
    classExpression match
      case nominal@Nominal(_) =>
        nominals contains nominal
      case successor@ObjectSomeValuesFrom(_@ObjectProperty(_), _@Nominal(_)) =>
        successors contains successor
      case _@Class(_) =>
        true
      case _ =>
        _representativeOf contains classExpression
  }

  private def ensureHasRepresentative(classExpression: OWLClassExpression): Unit = {
    // representativeOf.synchronized {
    if (!hasRepresentative(classExpression))
      addRepresentative(classExpression)
    // }
  }

  // representativeOf(OWLThing) = OWLThing
  representativeFor(OWLThing) = OWLThing
  print(" 4 ")
  classExpressions.foreach(addRepresentativeUnchecked)
  print(" 5 ")
  elkReasoner.flush()
  print(" 6 ")
  elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
  print(" 7 ")

  override def entails(axiom: ELAxiom): Boolean = {
    axiom match {
      case subClassOfAxiom: OWLSubClassOfAxiom => isSubsumedBy(subClassOfAxiom.getSubClass, subClassOfAxiom.getSuperClass)
      case classAssertionAxiom: OWLClassAssertionAxiom => isInstanceOf(classAssertionAxiom.getIndividual, classAssertionAxiom.getClassExpression)
      case objectPropertyAssertionAxiom: OWLObjectPropertyAssertionAxiom => elkReasoner.isEntailed(objectPropertyAssertionAxiom)
    }
  }

  override def isInstanceOf(individual: OWLIndividual, classExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(classExpression)
    types(individual).contains(classExpression)
  }

  override def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(superClassExpression)
    subsumers(subClassExpression).contains(superClassExpression)
  }

  override def types(individual: OWLIndividual): LazyList[OWLClassExpression] = {
    // TODO: treat anonymous individuals
    (if nominals contains Nominal(individual.asOWLNamedIndividual()) then LazyList(Nominal(individual.asOWLNamedIndividual())) else LazyList.empty) concat
      (successors.filter { case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) => elkReasoner.isEntailed(individual.asOWLNamedIndividual() Fact(property, target)); case _ => false }) concat
      elkReasoner.types(individual.asOWLNamedIndividual()).toScala(LazyList).map(representativeFor)
  }

  override def instances(classExpression: OWLClassExpression): LazyList[OWLNamedIndividual] = {
    ensureHasRepresentative(classExpression)
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

  override def subsumers(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
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

  override def subsumees(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
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

  override def lt(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.superClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

  override def equiv(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.equivalentClasses(representativeOf(x)).toScala(LazyList).map(representativeFor).contains(y)
  }

}

protected class LazyELReasoner(ontology: OWLOntology, // axioms: Iterable[ELAxiom],
                               initiallySuppliedClassExpressions: collection.Set[OWLClassExpression],
                               allowNewClassExpressions: Boolean = true,
                               onDisposal: () => Unit = () => {})
  extends ELReasoner(ontology, initiallySuppliedClassExpressions, allowNewClassExpressions, onDisposal) {

  private val classExpressions = mutable.HashSet.from(initiallySuppliedClassExpressions)

  println("Initializing ELReasonerV2 with " + classExpressions.size + " class expressions.")

  elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)

  override def addClassExpression(classExpression: OWLClassExpression): Unit =
    if allowNewClassExpressions then
      classExpressions += classExpression
    else
      throw RuntimeException("No new class expressions in the reasoner are allowed.")

  override def entails(axiom: ELAxiom): Boolean =
    elkReasoner.isEntailed(axiom)

  override def isInstanceOf(individual: OWLIndividual, classExpression: OWLClassExpression): Boolean =
    elkReasoner.isEntailed(individual Type classExpression)

  override def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean =
    elkReasoner.isEntailed(subClassExpression SubClassOf superClassExpression)

  override def types(individual: OWLIndividual): collection.Set[OWLClassExpression] =
    classExpressions.filter(isInstanceOf(individual, _))

  override def instances(classExpression: OWLClassExpression): LazyList[OWLNamedIndividual] =
    elkReasoner.instances(classExpression).toScala(LazyList)

  override def subsumees(classExpression: OWLClassExpression): collection.Set[OWLClassExpression] =
    classExpressions.filter(isSubsumedBy(_, classExpression))

  override def subsumers(classExpression: OWLClassExpression): collection.Set[OWLClassExpression] =
    classExpressions.filter(isSubsumedBy(classExpression, _))

  override def lt(x: OWLClassExpression, y: OWLClassExpression): Boolean =
    isSubsumedBy(x, y)

  override def equiv(x: OWLClassExpression, y: OWLClassExpression): Boolean =
    elkReasoner.isEntailed(x EquivalentTo y)

}
