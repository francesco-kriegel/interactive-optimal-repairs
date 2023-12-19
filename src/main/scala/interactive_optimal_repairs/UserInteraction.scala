package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Answer.*
import interactive_optimal_repairs.RepairType.premises
import interactive_optimal_repairs.Util.{ImplicitOWLClassExpression, Nominal}
import protege_components.ProtegeWorkerPool

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import javax.swing.JOptionPane
import scala.annotation.{nowarn, tailrec}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

//enum Strategy(val name: String, val description: String) {
//  case FAST extends Strategy("Fast", "Strategy as described in the JELIA 2023 paper, which constructs a repair seed with fewest number of questions.")
//  case SMARTv1 extends Strategy("Smart v1", "Experimental strategy that runs in three stages: first like the strategy Fast, then determines the difference between the saturated and the unsaturated repair induced by the repair seed from Phase 1, and finally again like strategy Fast but now for the declined queries from Phase 2.")
//  case SMARTv2 extends Strategy("Smart v2 (recommended)", "Recommended Strategy, which only generates questions in the enviroment of the provided unwanted consequences in the repair request. It runs in two stages: in Phase 1 premises/causes for the unwanted consequences are identified, in Phase 2 the difference between the saturated and the unsaturated repair induced by the repair seed from Phase 1 is determined to generate additional questions.  Simply put, these are axioms the deduction of which from the input ontology necessarily generates some of the axioms from Phase 1 identified as to be removed.")
//  case BEST extends Strategy("Best", "Strategy as described in the KR 2022 paper, which can construct every repair seed.")
//}

trait UserInterface {
  def showQuestion(query: Query): Unit
  def removeQuestion(query: Query): Unit
}

enum Answer {
  case ACCEPT, IGNORE, DECLINE, INHERITED_ACCEPT, INHERITED_DECLINE, ROLLBACK
}

//object UserInteraction {
//  def apply(strategy: Strategy)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager, p: ProtegeWorkerPool): UserInteraction =
//    strategy match
//      case FAST => FastUserInteraction()
//      case SMARTv1 => Smart1UserInteraction()
//      case SMARTv2 => Smart2UserInteraction()
//      case BEST => BestUserInteraction()
//}

abstract class UserInteraction()(using configuration: RepairConfiguration) {

  protected var userInterface: UserInterface = _
  def start(userInterface: UserInterface): Unit = {
    this.userInterface = userInterface
    initialize()
  }

  protected def initialize(): Unit
  def receiveAnswer(query: Query, answer: Answer): Unit
  def hasBeenCompleted: Boolean
  protected def getRepairSeedUnchecked: RepairSeed
  def getRepairSeed: RepairSeed = {
    if !hasBeenCompleted then
      throw IllegalStateException("A repair seed has not been determined since the user interaction has not been completed.")
    else
      getRepairSeedUnchecked
  }
  def getButtonTypes(query: Query): collection.Set[Answer]
  def dispose(): Unit

}

class SmartUserInteraction(val inheritedAnswersMustBeConfirmed: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager, p: ProtegeWorkerPool) extends UserInteraction() {

  private val isCurrentlyProcessing = AtomicInteger(0)
  @volatile private var inPhase2 = false

  private val roleAssertions = configuration.ontology.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION).asScala

  private val pendingQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val acceptedQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  acceptedQueries ++= configuration.request.positiveAxioms
  private val declinedQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val inheritedAnswers = ConcurrentHashMap[Query, Answer]().asScala

//  private val acceptedQueriesReasoner =
//    // TODO: Implement a variant of ELReasoner that supports multiple ABoxes with a shared TBox.
//    ExtendedClassification(
//      configuration.ontology.getTBoxAxioms(Imports.INCLUDED).asScala,
//      configuration.subClassExpressions,
//      false
//    )
  private val acceptedQueriesABoxIndex = configuration.classificationOfInputOntology.registerABox(configuration.request.positiveAxioms.asInstanceOf[collection.Set[OWLAxiom]])

  private def isUndecided(query: Query): Boolean = {
    !(acceptedQueries contains query) && !(declinedQueries contains query)
  }

  override def hasBeenCompleted: Boolean = {
    inPhase2 && (isCurrentlyProcessing.get() equals 0) && pendingQueries.isEmpty
  }

  private def getRepairSeedAfterPhase1: RepairSeed = {
    RepairSeed(true, declinedQueries collect {
      case axiom: OWLClassAssertionAxiom => axiom
    })
  }

  override protected def getRepairSeedUnchecked: RepairSeed = {
    RepairSeed(true, declinedQueries collect {
      case axiom: OWLClassAssertionAxiom => axiom
      case ObjectPropertyAssertion(_, property@ObjectProperty(_), subject@NamedIndividual(_), target@NamedIndividual(_)) =>
        val nominal = Nominal(target)
        val successor = property some nominal
        configuration.classificationOfEmptyOntology.addClassExpressions(Set(nominal, successor))
        configuration.classificationOfInputOntology.addClassExpressions(Set(nominal, successor))
        subject Type successor // standard translation of role assertions into class assertions, as used in the KR 2022 paper
    })
  }

  override def getButtonTypes(query: Query): collection.Set[Answer] = {
    if inheritedAnswers contains query then
      Set(inheritedAnswers(query), ROLLBACK)
    else
      Set(ACCEPT, DECLINE)
  }

  override protected def initialize(): Unit = {
    // processDeclinedQueries(configuration.request.axioms filter configuration.ontologyReasoner.entails, false)
    processDeclinedQueries(configuration.request.negativeAxioms, false)
    p.asynchronouslyInNewWorker("Waiting for completion of Phase 1...") {
      while !((isCurrentlyProcessing.get() equals 0) && pendingQueries.isEmpty) do Thread.sleep(100)
    } executeAndThen {
      p.asynchronouslyInNewWorker("Initializing Phase 2...") {
        initializePhase2()
        inPhase2 = true
      }.execute()
    }
  }

  private def initializePhase2(): Unit = {
    val seed = getRepairSeedAfterPhase1
    val saturatedRepairVirtual = IRQRepair(seed, true)
    val unsaturatedRepairComputed = IRQRepair(seed, false).compute(CompatibilityMode.FRESH_NAMED_INDIVIDUALS)
//    val unsaturatedRepairReasoner =
//      // TODO: Implement a variant of ELReasoner that supports multiple ABoxes with a shared TBox.
//      ExtendedClassification(
//        unsaturatedRepairComputed,
//        configuration.subClassExpressions,
//        false,
//        true)
    ontologyManager.addAxioms(unsaturatedRepairComputed, acceptedQueries.asJava)
    val unsaturatedRepairABoxIndex = configuration.classificationOfInputOntology.registerABox(unsaturatedRepairComputed, true)
    for {
      individual <- configuration.ontology.getIndividualsInSignature(Imports.INCLUDED).asScala
      // classExpression <- minimalElements(configuration.ontologyReasoner.types(individual), _ isSubsumedBy _ wrt configuration.trivialReasoner)
      classExpression <- configuration.classificationOfInputOntology.types(individual).filter(_.isAtom)
    }
      val query = individual Type classExpression
//      if isUndecided(query) && (saturatedRepair entails query) && !(unsaturatedRepairReasoner entails query) then
      if isUndecided(query) && (saturatedRepairVirtual entails query) && !configuration.classificationOfInputOntology.entails(unsaturatedRepairABoxIndex, query) then
        pendingQueries += query
        userInterface.showQuestion(query)
//    unsaturatedRepairReasoner.dispose()
    configuration.classificationOfInputOntology.unregisterABox(unsaturatedRepairABoxIndex)
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    if answer equals ROLLBACK then // TODO: Implement rollback functionality.
      JOptionPane.showMessageDialog(null, "Rollback has not been implemented.", "Error", JOptionPane.ERROR_MESSAGE)
    else
      isCurrentlyProcessing.incrementAndGet()
      userInterface.removeQuestion(query)
      pendingQueries -= query
      answer match
        case ACCEPT => processAcceptedQuery(query, false)
        case IGNORE => ??? // Should never occur.
        case DECLINE => processDeclinedQueries(Iterable.single(query), false)
        case INHERITED_ACCEPT => // Do nothing.
        case INHERITED_DECLINE => // Do nothing.
        case ROLLBACK => rollback(query)
      isCurrentlyProcessing.decrementAndGet()
  }

  private def processAcceptedQuery(query: Query, inheritedAccept: Boolean): Unit = {
    acceptedQueries += query
//    acceptedQueriesReasoner.addAxiomAndFlush(query)
    configuration.classificationOfInputOntology.addAxiomAndFlush(acceptedQueriesABoxIndex, query)
    if inheritedAccept then
      if inheritedAnswersMustBeConfirmed then
        inheritedAnswers(query) = INHERITED_ACCEPT
      else
        userInterface.removeQuestion(query)
        pendingQueries -= query
    findNewInheritedAnswers()
  }

  private def processDeclinedQueries(queries: Iterable[Query], inheritedDecline: Boolean): Unit = {
    val undecidedQueries_Conjunction = mutable.HashSet[OWLClassAssertionAxiom]()
    val undecidedQueries_ExistentialRestriction = mutable.HashSet[OWLClassAssertionAxiom]()

    val processedQueries = mutable.HashSet[Query]()
    @tailrec def recursivelyProcess(currentDeclinedQueries: Iterable[Query], inheritedDecline: Boolean): Unit = {
      processedQueries ++= currentDeclinedQueries
      val nextDeclinedQueries = mutable.HashSet[Query]()
      currentDeclinedQueries.foreach {
        case query@ClassAssertion(_, classExpression, individual) =>
          if classExpression.isAtom then
            declinedQueries += query
            if inheritedDecline then
              if inheritedAnswersMustBeConfirmed then
                inheritedAnswers(query) = INHERITED_DECLINE
              else
                userInterface.removeQuestion(query)
                pendingQueries -= query
            if classExpression.isObjectSomeValuesFrom then
              undecidedQueries_ExistentialRestriction += query
            //nextDeclinedQueries ++=
            //  premises(individual, classExpression) filterNot {
            //    _ isCoveredBy (declinedQueries collect { case ClassAssertion(_, dlassExpression, jndividual) if individual equals jndividual => dlassExpression }) wrt configuration.trivialReasoner
            //  } map {
            //    individual Type _
            //  }
            nextDeclinedQueries ++= premises(KernelObject(individual), classExpression) map { individual Type _ } diff processedQueries
          else
            undecidedQueries_Conjunction += query
        case query@ObjectPropertyAssertion(_, _, _, _) =>
          declinedQueries += query
          if inheritedDecline then
            if inheritedAnswersMustBeConfirmed then
              inheritedAnswers(query) = INHERITED_DECLINE
            else
              userInterface.removeQuestion(query)
              pendingQueries -= query
        case _ =>
          throw IllegalArgumentException("Unsupported query occurred in smart v2 user interaction.")
      }
      if nextDeclinedQueries.nonEmpty then
        recursivelyProcess(nextDeclinedQueries, true)
    }

    recursivelyProcess(queries, inheritedDecline)

    undecidedQueries_Conjunction.foreach {
      case _@ClassAssertion(_, classExpression, individual) =>
        classExpression.topLevelConjuncts().foreach {
          atom =>
            val query = individual Type atom
            if isUndecided(query) then
              pendingQueries += query
              userInterface.showQuestion(query)
        }
    }

    undecidedQueries_ExistentialRestriction.foreach {
      case ClassAssertion(_, ObjectSomeValuesFrom(property@ObjectProperty(_), filler), individual) =>
        roleAssertions.foreach {
          case roleAssertion@ObjectPropertyAssertion(_, qroperty, subject, target) =>
            if (property equals qroperty)
              && (individual equals subject) then
              // && !(filler isCoveredBy (declinedQueries collect { case ClassAssertion(_, dlassExpression, jndividual) if target equals jndividual => dlassExpression }) wrt configuration.trivialReasoner) then
                val classAssertion = target Type filler
                if isUndecided(classAssertion) then
                  pendingQueries += classAssertion
                  userInterface.showQuestion(classAssertion)
                if isUndecided(roleAssertion) then
                  pendingQueries += roleAssertion
                  userInterface.showQuestion(roleAssertion)
        }
    }

    findNewInheritedAnswers()
  }

  private def findNewInheritedAnswers(): Unit = {
    val nextDeclinedQueries = mutable.HashSet[Query]()
    (pendingQueries filterNot inheritedAnswers.keySet).foreach(query => {
//      if acceptedQueriesReasoner entails query then
      if configuration.classificationOfInputOntology.entails(acceptedQueriesABoxIndex, query) then
        processAcceptedQuery(query, true)
      else if {
//        acceptedQueriesReasoner.addAxiomAndFlush(query)
//        val inheritedDecline = declinedQueries.exists(acceptedQueriesReasoner.entails)
//        acceptedQueriesReasoner.removeAxiomAndFlush(query)
        configuration.classificationOfInputOntology.addAxiomAndFlush(acceptedQueriesABoxIndex, query)
        val inheritedDecline = declinedQueries.exists(configuration.classificationOfInputOntology.entails(acceptedQueriesABoxIndex, _))
        configuration.classificationOfInputOntology.removeAxiomAndFlush(acceptedQueriesABoxIndex, query)
        inheritedDecline
      } then
        nextDeclinedQueries += query
    })
    if nextDeclinedQueries.nonEmpty then
      processDeclinedQueries(nextDeclinedQueries, true)
  }

  private def rollback(query: Query): Unit = {
    if !(inheritedAnswers contains query) then throw RuntimeException("Unable to rollback for query " + query)
    { inheritedAnswers(query) match
        case INHERITED_ACCEPT =>
          // To be able to decline the query, wrongly accepted queries need to be identified.
          // Compute all justifications why `query` is entailed by `acceptedQueries`
        case INHERITED_DECLINE =>
          // To be able to accept the query, wrongly declined queries need to be identified.
//          acceptedQueriesReasoner.addAxiomAndFlush(query)
//          val candidates = declinedQueries.filter(acceptedQueriesReasoner.entails)
//          acceptedQueriesReasoner.removeAxiomAndFlush(query)
          configuration.classificationOfInputOntology.addAxiomAndFlush(acceptedQueriesABoxIndex, query)
          val candidates = declinedQueries.filter(configuration.classificationOfInputOntology.entails(acceptedQueriesABoxIndex, _))
          configuration.classificationOfInputOntology.removeAxiomAndFlush(acceptedQueriesABoxIndex, query)
    }: @nowarn
  }

  override def dispose(): Unit = {
//    acceptedQueriesReasoner.dispose()
    configuration.classificationOfInputOntology.unregisterABox(acceptedQueriesABoxIndex)
  }

}


