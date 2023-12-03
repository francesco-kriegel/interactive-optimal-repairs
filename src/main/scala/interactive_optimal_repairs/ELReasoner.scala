package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*
import interactive_optimal_repairs.Util.Nominal

import org.phenoscape.scowl.*
import org.semanticweb.elk.owlapi.{ElkReasoner, ElkReasonerFactory}
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.reasoner.InferenceType

import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*

type ELAxiom = OWLSubClassOfAxiom | OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom

class ExtendedClassification(ontology: OWLOntology,
                             classExpressions: collection.Set[OWLClassExpression],
                             allowNewClassExpressions: Boolean,
                             ontologyWillNotBeAccessedOtherwise: Boolean = false)
                            (using ontologyManager: OWLOntologyManager)
  extends PartialOrdering[OWLClassExpression] {

  protected val localOntology: OWLOntology = if ontologyWillNotBeAccessedOtherwise then ontology else ontologyManager.createOntology(ontology.getAxioms)

  def this(axioms: collection.Set[_ <: OWLAxiom],
           classExpressions: collection.Set[OWLClassExpression],
           allowNewClassExpressions: Boolean)
          (using ontologyManager: OWLOntologyManager) = {
    this(
      ontologyManager.createOntology(axioms.asInstanceOf[collection.Set[OWLAxiom]].asJava),
      classExpressions,
      allowNewClassExpressions,
      true)
  }

  protected def addAxiom(axiom: ELAxiom): Unit = {
    localOntology.addAxiom(axiom)
  }

  def addAxiomAndFlush(axiom: ELAxiom): Unit = {
    addAxiom(axiom)
    elkReasoner.flush()
  }

  protected def removeAxiom(axiom: ELAxiom): Unit = {
    localOntology.removeAxiom(axiom)
  }

  def removeAxiomAndFlush(axiom: ELAxiom): Unit = {
    removeAxiom(axiom)
    elkReasoner.flush()
  }

  protected val elkReasoner: ElkReasoner = ElkReasonerFactory().createReasoner(localOntology)
  // elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)

  def dispose(): Unit = {
    elkReasoner.dispose()
    ontologyManager.removeOntology(localOntology)
    _representativeOf.clear()
    representativeFor.clear()
    nominals.clear()
    successors.clear()
  }

  private val _representativeOf = java.util.concurrent.ConcurrentHashMap[OWLClassExpression, OWLClass]().asScala // mutable.HashMap[OWLClassExpression, OWLClass]()
  private val representativeFor = java.util.concurrent.ConcurrentHashMap[OWLClass, OWLClassExpression]().asScala // mutable.HashMap[OWLClass, OWLClassExpression]()

  private def representativeOf(classExpression: OWLClassExpression): OWLClass = {
    classExpression match
      case c@Class(_) => c
      case _ => _representativeOf(classExpression)
  }

  protected val nominals: mutable.Set[OWLObjectOneOf] = java.util.concurrent.ConcurrentHashMap.newKeySet[OWLObjectOneOf]().asScala // mutable.HashSet[OWLObjectOneOf]()
  protected val successors: mutable.Set[OWLObjectSomeValuesFrom] = java.util.concurrent.ConcurrentHashMap.newKeySet[OWLObjectSomeValuesFrom]().asScala // mutable.HashSet[OWLObjectSomeValuesFrom]()

  def addClassExpression(classExpression: OWLClassExpression): Unit = {
    if (allowNewClassExpressions)
      addRepresentativeUnchecked(classExpression)
      elkReasoner.flush()
    else
      throw new RuntimeException("No new class expressions in the reasoner are allowed.")
  }

  def addClassExpressions(classExpressions: collection.Set[OWLClassExpression]): Unit = {
    if (allowNewClassExpressions)
      classExpressions.foreach(addRepresentativeUnchecked)
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
      //            case _ => Class("internal_representative_class_of#" + classExpression)
      //        representativeOf(classExpression) = representative
      //        representativeFor(representative) = classExpression
      //        if (!(classExpression equals representative))
      //          ontology.addAxiom(EquivalentClasses(representative, classExpression))
      case c@Class(_) =>
        // representativeOf(c) = c
        // representativeFor(c) = c
      case _ =>
        val representative = Class("internal_representative_class_of#" + classExpression)
        _representativeOf(classExpression) = representative
        representativeFor(representative) = classExpression
        localOntology.addAxiom(representative EquivalentTo classExpression)
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
      addClassExpression(classExpression)
    // }
  }

  // representativeOf(OWLThing) = OWLThing
  // representativeFor(OWLThing) = OWLThing
  classExpressions.foreach(addRepresentativeUnchecked)
  elkReasoner.flush()
  elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)

  def precomputeInferences(): Unit = {
    elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
  }

  def entails(axiom: ELAxiom): Boolean = {
//    axiom match {
//      case SubClassOf(_, subClass, superClass) => isSubsumedBy(subClass, superClass)
//      case ClassAssertion(_, classExpression, individual) => isInstanceOf(individual, classExpression)
//      case objectPropertyAssertionAxiom: OWLObjectPropertyAssertionAxiom => elkReasoner.isEntailed(objectPropertyAssertionAxiom)
//    }
    elkReasoner.isEntailed(axiom)
  }

  def isInstanceOf(individual: OWLIndividual, classExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(classExpression)
    types(individual).contains(classExpression)
  }

  def isSubsumedBy(subClassExpression: OWLClassExpression, superClassExpression: OWLClassExpression): Boolean = {
    ensureHasRepresentative(superClassExpression)
    subsumers(subClassExpression).contains(superClassExpression)
  }

  def types(individual: OWLIndividual): LazyList[OWLClassExpression] = {
    // TODO: treat anonymous individuals
    (if nominals contains Nominal(individual.asOWLNamedIndividual()) then LazyList(Nominal(individual.asOWLNamedIndividual())) else LazyList.empty) concat
      successors.filter { case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) => elkReasoner.isEntailed(individual.asOWLNamedIndividual() Fact(property, target)); case _ => false } concat
      elkReasoner.types(individual.asOWLNamedIndividual()).toScala(LazyList).map(representativeFor.orElse(c => c))
  }

  def instances(classExpression: OWLClassExpression): LazyList[OWLIndividual] = {
    ensureHasRepresentative(classExpression)
    classExpression match
      case Nominal(individual) =>
        LazyList(individual)
      case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) =>
        localOntology.getABoxAxioms(Imports.INCLUDED).stream().toScala(LazyList).collect {
          case ObjectPropertyAssertion(_, qroperty, subject, uarget) if (property equals qroperty) && (target equals uarget) => subject
        }
      case _ =>
        elkReasoner.instances(representativeOf(classExpression)).toScala(LazyList)
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
        ).toScala(LazyList).map(representativeFor.orElse(c => c))
  }

  def subsumees(classExpression: OWLClassExpression): LazyList[OWLClassExpression] = {
    ensureHasRepresentative(classExpression)
    classExpression match
      case nominal@Nominal(_) =>
        LazyList(nominal)
      case ObjectSomeValuesFrom(property@ObjectProperty(_), _@Nominal(target)) =>
        localOntology.getABoxAxioms(Imports.INCLUDED).stream().toScala(LazyList).collect {
          case ObjectPropertyAssertion(_, qroperty, subject@NamedIndividual(_), uarget) if (property equals qroperty) && (target equals uarget) => Nominal(subject)
        }
      case _ =>
        java.util.stream.Stream.concat(
          elkReasoner.equivalentClasses(representativeOf(classExpression)),
          elkReasoner.subClasses(representativeOf(classExpression))
        ).toScala(LazyList).filterNot(_ equals OWLNothing).map(representativeFor.orElse(c => c))
  }

  override def tryCompare(x: OWLClassExpression, y: OWLClassExpression): Option[Int] = {
    if (lt(x, y)) Some(-1)
    else if (equiv(x, y)) Some(0)
    else if (gt(x, y)) Some(1)
    else None
  }

  override def lt(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.superClasses(representativeOf(x)).toScala(LazyList).map(representativeFor.orElse(c => c)).contains(y)
  }

  override def equiv(x: OWLClassExpression, y: OWLClassExpression): Boolean = {
    ensureHasRepresentative(x)
    ensureHasRepresentative(y)
    elkReasoner.equivalentClasses(representativeOf(x)).toScala(LazyList).map(representativeFor.orElse(c => c)).contains(y)
  }

  override def lteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || lt(x, y)

  override def gteq(x: OWLClassExpression, y: OWLClassExpression): Boolean = equiv(x, y) || gt(x, y)

  override def gt(x: OWLClassExpression, y: OWLClassExpression): Boolean = lt(y, x)

}

private class ExtendedClassificationForMultipleABoxesWithSharedTBox(ontology: OWLOntology,
                                                                    classExpressions: collection.Set[OWLClassExpression],
                                                                    allowNewClassExpressions: Boolean,
                                                                    ontologyWillNotBeAccessedOtherwise: Boolean = false)
                                                                   (using ontologyManager: OWLOntologyManager)
  extends ExtendedClassification(ontology, classExpressions, allowNewClassExpressions, ontologyWillNotBeAccessedOtherwise) {

  def this(axioms: collection.Set[_ <: OWLAxiom],
           classExpressions: collection.Set[OWLClassExpression],
           allowNewClassExpressions: Boolean)
          (using ontologyManager: OWLOntologyManager) = {
    this(
      ontologyManager.createOntology(axioms.asInstanceOf[collection.Set[OWLAxiom]].asJava),
      classExpressions,
      allowNewClassExpressions,
      true)
  }

  private val iRepresentativeOfMaps = mutable.ArrayBuffer[mutable.Map[OWLIndividual, OWLIndividual]]()
  private val iRepresentativeForMaps = mutable.ArrayBuffer[mutable.Map[OWLIndividual, OWLIndividual]]()

//  private val individualsInInitialABox = mutable.HashSet.from[OWLIndividual](ontology.getIndividualsInSignature(Imports.INCLUDED).asScala ++ ontology.getAnonymousIndividuals.asScala)
  private val individualsInInitialABox = java.util.concurrent.ConcurrentHashMap.newKeySet[OWLIndividual]().asScala
  individualsInInitialABox ++= ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
  individualsInInitialABox ++= ontology.getAnonymousIndividuals.asScala

  private var currentABoxIndex = -1
  private val unregisteredABoxIndices = java.util.concurrent.ConcurrentHashMap.newKeySet[Integer]().asScala // mutable.HashSet[Integer]()

  private def checkABoxIndex(aboxIndex: Integer): Unit = {
    if !(0 <= aboxIndex && aboxIndex <= currentABoxIndex) || (unregisteredABoxIndices contains aboxIndex) then
      throw IllegalArgumentException()
  }

  def registerABox(abox: OWLOntology, disposeOfABox: Boolean = false): Integer = {
    currentABoxIndex += 1
    val iRepresentativeOf = java.util.concurrent.ConcurrentHashMap[OWLIndividual, OWLIndividual]().asScala // mutable.HashMap[OWLIndividual, OWLIndividual]()
    val iRepresentativeFor = java.util.concurrent.ConcurrentHashMap[OWLIndividual, OWLIndividual]().asScala // mutable.HashMap[OWLIndividual, OWLIndividual]()
    iRepresentativeOfMaps += iRepresentativeOf
    iRepresentativeForMaps += iRepresentativeFor

    val individuals = abox.getIndividualsInSignature(Imports.INCLUDED).asScala ++ abox.getAnonymousIndividuals.asScala
    individuals.foreach { individual =>
      val representative = Individual("abox_" + currentABoxIndex + "_internal_representative_individual_of#" + individual)
      iRepresentativeOf(individual) = representative
      iRepresentativeFor(representative) = individual
    }

    val axioms = abox.getABoxAxioms(Imports.INCLUDED).asScala
    axioms.foreach {
      case ClassAssertion(_, classExpression, individual) =>
        super.addAxiom(iRepresentativeOf(individual) Type classExpression)
      case ObjectPropertyAssertion(_, property, subject, target) =>
        super.addAxiom(iRepresentativeOf(subject) Fact (property, iRepresentativeOf(target)))
    }
    elkReasoner.flush()
    elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)

    if disposeOfABox then
      ontologyManager.removeOntology(abox)

    currentABoxIndex
  }

  def registerABox(axioms: collection.Set[OWLAxiom]): Integer = {
    registerABox(ontologyManager.createOntology(axioms.asJava), true)
  }

  def unregisterABox(aboxIndex: Integer): Unit = {
    clearABox(aboxIndex)
    unregisteredABoxIndices += aboxIndex
  }

  def clearABox(aboxIndex: Integer): Unit = {
    replaceABox(aboxIndex, Set.empty)
  }

  def replaceABox(aboxIndex: Integer, axioms: collection.Set[OWLAxiom]): Unit = {
    checkABoxIndex(aboxIndex)
    iRepresentativeForMaps(aboxIndex).keySet.foreach { representative =>
      ontologyManager.removeAxioms(localOntology, localOntology.getAxioms(representative, Imports.EXCLUDED))
    }
    iRepresentativeOfMaps(aboxIndex).clear()
    iRepresentativeForMaps(aboxIndex).clear()
    axioms.foreach {
      case ClassAssertion(_, classExpression, individual) =>
        super.addAxiom(getRepresentativeOf(aboxIndex, individual) Type classExpression)
      case ObjectPropertyAssertion(_, property, subject, target) =>
        super.addAxiom(getRepresentativeOf(aboxIndex, subject) Fact(property, getRepresentativeOf(aboxIndex, target)))
    }
    elkReasoner.flush()
    elkReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
  }

  private def getRepresentativeOf(aboxIndex: Integer, individual: OWLIndividual): OWLIndividual = {
    //checkABoxIndex(aboxIndex)
    if !(iRepresentativeOfMaps(aboxIndex) contains individual) then
      val representative = Individual("abox_" + aboxIndex + "_internal_representative_individual_of#" + individual)
      iRepresentativeOfMaps(aboxIndex)(individual) = representative
      iRepresentativeForMaps(aboxIndex)(representative) = individual
      representative
    else
      iRepresentativeOfMaps(aboxIndex)(individual)
  }

  override protected def addAxiom(axiom: ELAxiom): Unit = {
    axiom match
      case ClassAssertion(_, _, individual) =>
        individualsInInitialABox += individual
      case ObjectPropertyAssertion(_, _, subject, target) =>
        individualsInInitialABox += subject
        individualsInInitialABox += target
      case _ =>
        // Do nothing.
    super.addAxiom(axiom)
  }

  override def addAxiomAndFlush(axiom: ELAxiom): Unit = {
    addAxiom(axiom)
    elkReasoner.flush()
  }

  private def translateAxiom(aboxIndex: Integer, axiom: ELAxiom): ELAxiom = {
    axiom match
      case ClassAssertion(_, classExpression, individual) =>
        getRepresentativeOf(aboxIndex, individual) Type classExpression
      case ObjectPropertyAssertion(_, property, subject, target) =>
        getRepresentativeOf(aboxIndex, subject) Fact(property, getRepresentativeOf(aboxIndex, target))
      case _ =>
        axiom
  }

  def addAxiomAndFlush(aboxIndex: Integer, axiom: ELAxiom): Unit = {
    checkABoxIndex(aboxIndex)
    super.addAxiomAndFlush(translateAxiom(aboxIndex, axiom))
  }

  def removeAxiomAndFlush(aboxIndex: Integer, axiom: ELAxiom): Unit = {
    checkABoxIndex(aboxIndex)
    removeAxiomAndFlush(translateAxiom(aboxIndex, axiom))
  }

  def entails(aboxIndex: Integer, axiom: ELAxiom): Boolean = {
    checkABoxIndex(aboxIndex)
    entails(translateAxiom(aboxIndex, axiom))
  }

  def isInstanceOf(aboxIndex: Integer, individual: OWLIndividual, classExpression: OWLClassExpression): Boolean = {
    checkABoxIndex(aboxIndex)
    isInstanceOf(getRepresentativeOf(aboxIndex, individual), classExpression)
  }

  def types(aboxIndex: Integer, individual: OWLIndividual): LazyList[OWLClassExpression] = {
    checkABoxIndex(aboxIndex)
    types(getRepresentativeOf(aboxIndex, individual))
  }

  override def instances(classExpression: OWLClassExpression): LazyList[OWLIndividual] = {
    super.instances(classExpression) filter individualsInInitialABox
  }

  def instances(aboxIndex: Integer, classExpression: OWLClassExpression): LazyList[OWLIndividual] = {
    checkABoxIndex(aboxIndex)
    super.instances(classExpression) collect iRepresentativeForMaps(aboxIndex)
  }

  override def dispose(): Unit = {
    super.dispose()
    iRepresentativeOfMaps.clear()
    iRepresentativeForMaps.clear()
    individualsInInitialABox.clear()
    unregisteredABoxIndices.clear()
  }

}
