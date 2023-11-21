package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Answer.*
import interactive_optimal_repairs.RepairType.premises
import interactive_optimal_repairs.Strategy.*
import interactive_optimal_repairs.Util.ImplicitOWLClassExpression
import protege_components.ProtegeWorker.asynchronouslyInNewWorker

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import javax.swing.JOptionPane
import scala.annotation.{nowarn, tailrec}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

enum Strategy(val name: String, val description: String) {
  case FAST extends Strategy("Fast", "Strategy as described in the JELIA 2023 paper, which constructs a repair seed with fewest number of questions.")
  case SMARTv1 extends Strategy("Smart v1", "Experimental strategy that runs in three stages: first like the strategy Fast, then determines the difference between the saturated and the unsaturated repair induced by the repair seed from Phase 1, and finally again like strategy Fast but now for the declined queries from Phase 2.")
  case SMARTv2 extends Strategy("Smart v2", "TBA")
  case BEST extends Strategy("Best", "Strategy as described in the KR 2022 paper, which can construct every repair seed.")
}

trait UserInterface {
  def showQuestion(query: Query): Unit
  def removeQuestion(query: Query): Unit
}

enum Answer {
  case ACCEPT, IGNORE, DECLINE, INHERITED_ACCEPT, INHERITED_DECLINE, ROLLBACK
}

object UserInteraction {
  def apply(strategy: Strategy)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager): UserInteraction =
    strategy match
      case FAST => FastUserInteraction()
      case SMARTv1 => Smart1UserInteraction()
      case SMARTv2 => Smart2UserInteraction()
      case BEST => BestUserInteraction()
}

abstract class UserInteraction()(using configuration: RepairConfiguration) {

  protected var userInterface: UserInterface = _
  def start(userInterface: UserInterface): Unit = {
    this.userInterface = userInterface
    initialize()
  }

  protected def initialize(): Unit
  def receiveAnswer(query: Query, answer: Answer): Unit
  def hasBeenCompleted(): Boolean
  protected def getRepairSeedUnchecked(): RepairSeed
  def getRepairSeed(): RepairSeed = {
    if !hasBeenCompleted() then
      throw IllegalStateException("A repair seed has not been determined since the user interaction has not been completed.")
    else
      getRepairSeedUnchecked()
  }
  def getButtonTypes(query: Query): collection.Set[Answer]
  def dispose(): Unit

}

/* This strategy is described in the JELIA 2023 paper. */
class FastUserInteraction()(using configuration: RepairConfiguration) extends UserInteraction() {

  protected val repairSeed = mutable.HashMap[OWLNamedIndividual, mutable.HashSet[OWLClassExpression]]()
  protected val nonDeclinedRoleAssertions = ConcurrentHashMap.newKeySet[OWLObjectPropertyAssertionAxiom]().asScala
  protected val pendingQueries_Conjunction = ConcurrentHashMap[OWLClassAssertionAxiom, mutable.HashSet[OWLClassAssertionAxiom]]().asScala
              // contains entries a:C₁⊓...⊓Cₙ ⟼ a:C₁ | ... | a:Cₙ
  protected val pendingQueries_ExistentialRestriction = ConcurrentHashMap[(OWLIndividual, OWLObjectProperty, OWLIndividual, OWLClassExpression), (OWLObjectPropertyAssertionAxiom, OWLClassAssertionAxiom)]().asScala
              // contains entries (a,r,b,C) ⟼ (a,b):r | b:C
  protected val isCurrentlyProcessing = AtomicInteger(0)

  protected def processDeclinedQueries(queries: Iterable[Query]): Unit = {
    val undecidedQueries_Conjunction = mutable.HashSet[OWLClassAssertionAxiom]()
    val undecidedQueries_ExistentialRestriction = mutable.HashSet[OWLClassAssertionAxiom]()
    @tailrec def recursivelyProcess(qs: Iterable[Query]): Unit = {
      val ps = mutable.HashSet[Query]()
      qs.foreach {
        case classAssertion @ ClassAssertion(_, classExpression, individual) =>
          if classExpression.isAtom then
            repairSeed.getOrElseUpdate(individual.asOWLNamedIndividual(), { mutable.HashSet[OWLClassExpression]() }).add(classExpression)

            val implicitlyAnsweredQueries_Conjunction =
              pendingQueries_Conjunction.keySet filter {
                case ClassAssertion(_, dlassExpression, jndividual) =>
                  (individual eq jndividual) && (dlassExpression isSubsumedBy classExpression wrt configuration.trivialReasoner)
                case _ => ???
              }
            val diff_Conjunction = pendingQueries_Conjunction.keySet diff implicitlyAnsweredQueries_Conjunction
            val subQueriesToBeRetained_Conjunction = pendingQueries_Conjunction.flatMap((query, subQueries) => if diff_Conjunction contains query then subQueries else collection.Set.empty).toSet
            implicitlyAnsweredQueries_Conjunction.foreach { pendingQueries_Conjunction(_).filterNot { subQueriesToBeRetained_Conjunction } foreach { userInterface.removeQuestion } }
            pendingQueries_Conjunction --= implicitlyAnsweredQueries_Conjunction

            val implicitlyAnsweredQueries_ExistentialRestriction =
              pendingQueries_ExistentialRestriction.keySet filter {
                case (_, _, target, filler) => (individual equals target) && (filler isSubsumedBy classExpression wrt configuration.trivialReasoner)
              }
            val diff_ExistentialRestriction = pendingQueries_ExistentialRestriction.keySet diff implicitlyAnsweredQueries_ExistentialRestriction
            val subQueriesToBeRetained_ExistentialRestriction = pendingQueries_ExistentialRestriction.collect({ case (key, (roleAssertion, _)) if diff_ExistentialRestriction contains key => roleAssertion }).toSet[Query]
            implicitlyAnsweredQueries_ExistentialRestriction.foreach { pendingQueries_ExistentialRestriction(_).productIterator.map(_.asInstanceOf[Query]).filterNot { subQueriesToBeRetained_ExistentialRestriction } foreach { userInterface.removeQuestion } }
            pendingQueries_ExistentialRestriction --= implicitlyAnsweredQueries_ExistentialRestriction

            ps ++=
              premises(individual, classExpression) filterNot {
                _ isCoveredBy repairSeed.getOrElse(individual.asOWLNamedIndividual(), { mutable.HashSet.empty }) wrt configuration.trivialReasoner
              } map { individual Type _ }
            classExpression match
              case ObjectSomeValuesFrom(_, _) =>
                undecidedQueries_ExistentialRestriction += classAssertion
              case _ => // Do nothing.
          else
            undecidedQueries_Conjunction += classAssertion
        case roleAssertion @ ObjectPropertyAssertion(_, _, _, _) =>
          nonDeclinedRoleAssertions -= roleAssertion
          pendingQueries_ExistentialRestriction filter {
            case (_, (soleAssertion, _)) => roleAssertion equals soleAssertion
          } foreach {
            case (key, (roleAssertion, classAssertion)) =>
              userInterface.removeQuestion(roleAssertion)
              userInterface.removeQuestion(classAssertion)
              pendingQueries_ExistentialRestriction -= key
          }
        case _ =>
          throw IllegalArgumentException("Unsupported query occurred in fast user interaction.")
      }
      if ps.nonEmpty then recursivelyProcess(ps)
    }
    recursivelyProcess(queries)

    undecidedQueries_Conjunction --= pendingQueries_Conjunction.keySet
    undecidedQueries_Conjunction.filterInPlace {
      case ClassAssertion(_, classExpression, individual) =>
        !(classExpression isCoveredBy repairSeed.getOrElse(individual.asOWLNamedIndividual(), { mutable.HashSet.empty }) wrt configuration.trivialReasoner)
      case _ => ???
    }
    undecidedQueries_Conjunction.foreach {
      case assertion @ ClassAssertion(_, classExpression, individual) =>
        pendingQueries_Conjunction(assertion) = mutable.HashSet[OWLClassAssertionAxiom]()
        classExpression.topLevelConjuncts().foreach { atom => pendingQueries_Conjunction(assertion) += (individual Type atom) }
        pendingQueries_Conjunction(assertion).foreach { userInterface.showQuestion }
      case _ => ???
    }

    undecidedQueries_ExistentialRestriction.foreach {
      case ClassAssertion(_, ObjectSomeValuesFrom(property @ ObjectProperty(_), filler), individual) =>
        nonDeclinedRoleAssertions.foreach {
          case roleAssertion @ ObjectPropertyAssertion(_, qroperty, subject, target)
            if (property equals qroperty)
              && (individual equals subject)
              && !(pendingQueries_ExistentialRestriction contains (individual, property, target, filler))
              && !(filler isCoveredBy repairSeed.getOrElse(target.asOWLNamedIndividual(), { mutable.HashSet.empty }) wrt configuration.trivialReasoner) =>
            val classAssertion = target Type filler
            pendingQueries_ExistentialRestriction((individual, property, target, filler)) = (roleAssertion, classAssertion)
            userInterface.showQuestion(roleAssertion)
            userInterface.showQuestion(classAssertion)
          case _ => // Do nothing.
        }
      case _ => ???
    }
  }

  override protected def initialize(): Unit = {
    configuration.axioms.foreach {
      case roleAssertion: OWLObjectPropertyAssertionAxiom => nonDeclinedRoleAssertions += roleAssertion
      case _ => // Do nothing.
    }
    processDeclinedQueries(configuration.request.axioms.filter { configuration.ontologyReasoner.entails })
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    isCurrentlyProcessing.incrementAndGet()
    userInterface.removeQuestion(query)
    answer match
      case DECLINE => processDeclinedQueries(Iterable.single(query))
      case _ => ??? // Should never occur.
    isCurrentlyProcessing.decrementAndGet()
  }

  override def hasBeenCompleted(): Boolean = {
    isCurrentlyProcessing.get() == 0 && pendingQueries_Conjunction.isEmpty && pendingQueries_ExistentialRestriction.isEmpty
  }

  override protected def getRepairSeedUnchecked(): RepairSeed = {
    val axioms = repairSeed.flatMap((individual, atoms) => atoms.map(atom => individual Type atom))
    RepairSeed(true, axioms.toSeq: _*)
  }

  override def getButtonTypes(query: Query): collection.Set[Answer] = {
    Set(DECLINE)
  }

  override def dispose(): Unit = {
    // Do nothing.
  }

}

class Smart1UserInteraction()(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends FastUserInteraction() {

  private var phase = 1
  private val pendingPhase2Queries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val declinedPhase2Queries = ConcurrentHashMap.newKeySet[Query]().asScala

  override def start(userInterface: UserInterface): Unit = {
    super.start(userInterface)
    println("Phase 1 running ...")
    asynchronouslyInNewWorker {
      while !super.hasBeenCompleted() do Thread.sleep(100)
    } executeAndThen {
      println("Initializing phase 2 ...")
      initializePhase2()
      phase = 2
      println("Phase 2 running ...")
      asynchronouslyInNewWorker {
        while pendingPhase2Queries.nonEmpty do Thread.sleep(100)
      } executeAndThen {
        println("Initializing phase 3 ...")
        initializePhase3()
        phase = 3
        println("Phase 3 running ...")
      }
    }
  }

  private def initializePhase2(): Unit = {
    val seed = getRepairSeedUnchecked()
    val saturatedRepair = IQRepair(seed, true)
    val unsaturatedRepair = IQRepair(seed, false)
    val unsaturatedRepairReasoner =
      ELReasoner(
        unsaturatedRepair.compute(CompatibilityMode.FRESH_NAMED_INDIVIDUALS).getAxioms(Imports.INCLUDED).asScala.collect {
          case classAssertion: OWLClassAssertionAxiom => classAssertion
          case propertyAssertion: OWLObjectPropertyAssertionAxiom => propertyAssertion
          case classInclusion: OWLSubClassOfAxiom => classInclusion
        },
        configuration.subClassExpressions)

    for {
      individual <- configuration.ontologyReasoner.instances(OWLThing)
      // classExpression <- minimalElements(configuration.ontologyReasoner.types(individual), _ isSubsumedBy _ wrt configuration.trivialReasoner)
      classExpression <- configuration.ontologyReasoner.types(individual)
    }
      val assertion = individual Type classExpression
      if (saturatedRepair entails assertion) && !(unsaturatedRepairReasoner entails assertion) then
        pendingPhase2Queries += assertion
        userInterface.showQuestion(assertion)
    unsaturatedRepairReasoner.dispose()
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    if (phase equals 2) then
      isCurrentlyProcessing.incrementAndGet()
      pendingPhase2Queries -= query
      userInterface.removeQuestion(query)
      answer match
        case IGNORE => // Do nothing.
        case DECLINE => declinedPhase2Queries += query
        case _ => ??? // Should never occur.
      isCurrentlyProcessing.decrementAndGet()
    else
      super.receiveAnswer(query, answer)
  }

  private def initializePhase3(): Unit = {
    processDeclinedQueries(declinedPhase2Queries)
  }

  override def hasBeenCompleted(): Boolean = {
    (phase equals 3) && super.hasBeenCompleted()
  }

  override def getButtonTypes(query: Query): collection.Set[Answer] = {
    if phase equals 2 then
      Set(IGNORE, DECLINE)
    else
      Set(DECLINE)
  }

  override def dispose(): Unit = {
    // Do nothing.
  }

}

class Smart2UserInteraction(val inheritedAnswersMustBeConfirmed: Boolean = true)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends UserInteraction() {

  private val isCurrentlyProcessing = AtomicInteger(0)
  @volatile private var inPhase2 = false

  private val roleAssertions = configuration.axioms collect { case ax: OWLObjectPropertyAssertionAxiom => ax }

  private val pendingQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val acceptedQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val declinedQueries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val inheritedAnswers = ConcurrentHashMap[Query, Answer]().asScala

  private val acceptedQueriesReasoner =
    ELReasoner(
      configuration.axioms collect { case ax: OWLSubClassOfAxiom => ax },
      configuration.subClassExpressions,
      false
    )

  private def isUndecided(query: Query): Boolean = {
    !(acceptedQueries contains query) && !(declinedQueries contains query)
  }

  override def hasBeenCompleted(): Boolean = {
    inPhase2 && (isCurrentlyProcessing.get() equals 0) && pendingQueries.isEmpty
  }

  override protected def getRepairSeedUnchecked(): RepairSeed = {
    RepairSeed(true, declinedQueries collect { case ax: OWLClassAssertionAxiom => ax })
  }

  override def getButtonTypes(query: Query): collection.Set[Answer] = {
    if inheritedAnswers contains query then
      Set(inheritedAnswers(query), ROLLBACK)
    else
      Set(ACCEPT, DECLINE)
  }

  override protected def initialize(): Unit = {
    println("Initializing phase 1 ...")
    // processDeclinedQueries(configuration.request.axioms filter configuration.ontologyReasoner.entails, false)
    processDeclinedQueries(configuration.request.axioms, false)
    println("Phase 1 running ...")
    asynchronouslyInNewWorker {
      while !((isCurrentlyProcessing.get() equals 0) && pendingQueries.isEmpty) do Thread.sleep(100)
    } executeAndThen {
      println("Initializing phase 2 ...")
      initializePhase2()
      inPhase2 = true
      println("Phase 2 running ...")
    }
  }

  private def initializePhase2(): Unit = {
    val seed = getRepairSeedUnchecked()
    val saturatedRepair = IQRepair(seed, true)
    val unsaturatedRepair = IQRepair(seed, false)
    val unsaturatedRepairReasoner =
      ELReasoner(
        unsaturatedRepair.compute(CompatibilityMode.FRESH_NAMED_INDIVIDUALS).getAxioms(Imports.INCLUDED).asScala.collect {
          case classAssertion: OWLClassAssertionAxiom => classAssertion
          case propertyAssertion: OWLObjectPropertyAssertionAxiom => propertyAssertion
          case classInclusion: OWLSubClassOfAxiom => classInclusion
        },
        configuration.subClassExpressions)

    for {
      individual <- configuration.ontologyReasoner.instances(OWLThing)
      // classExpression <- minimalElements(configuration.ontologyReasoner.types(individual), _ isSubsumedBy _ wrt configuration.trivialReasoner)
      classExpression <- configuration.ontologyReasoner.types(individual)
    }
      val query = individual Type classExpression
      if isUndecided(query) && (saturatedRepair entails query) && !(unsaturatedRepairReasoner entails query) then
        pendingQueries += query
        userInterface.showQuestion(query)
    unsaturatedRepairReasoner.dispose()
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    if answer equals ROLLBACK then
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
    acceptedQueriesReasoner.addAxiomAndFlush(query)
    if inheritedAccept then
      if inheritedAnswersMustBeConfirmed then
        inheritedAnswers(query) = INHERITED_ACCEPT
      else
        userInterface.removeQuestion(query)
        pendingQueries -= query
    findNewInheritedAnswers()
  }

  private def processDeclinedQueries(queries: Iterable[Query], inheritedDecline: Boolean): Unit = {
    print("processing declined queries")
    val undecidedQueries_Conjunction = mutable.HashSet[OWLClassAssertionAxiom]()
    val undecidedQueries_ExistentialRestriction = mutable.HashSet[OWLClassAssertionAxiom]()

    val processedQueries = mutable.HashSet[Query]()
    @tailrec def recursivelyProcess(currentDeclinedQueries: Iterable[Query], inheritedDecline: Boolean): Unit = {
      print(".")
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
            nextDeclinedQueries ++= premises(individual, classExpression) map { individual Type _ } diff processedQueries
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
    println()
    print("Generating questions")

    undecidedQueries_Conjunction.foreach {
      case _@ClassAssertion(_, classExpression, individual) =>
        print(".")
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
        print(".")
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

    println()

    findNewInheritedAnswers()
  }

  private def findNewInheritedAnswers(): Unit = {
    val nextDeclinedQueries = mutable.HashSet[Query]()
    (pendingQueries filterNot inheritedAnswers.keySet).foreach(query => {
      if acceptedQueriesReasoner entails query then
        processAcceptedQuery(query, true)
      else if {
        acceptedQueriesReasoner.addAxiomAndFlush(query)
        val inheritedDecline = declinedQueries.exists(acceptedQueriesReasoner.entails)
        acceptedQueriesReasoner.removeAxiomAndFlush(query)
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
          acceptedQueriesReasoner.addAxiomAndFlush(query)
          val candidates = declinedQueries.filter(acceptedQueriesReasoner.entails)
          acceptedQueriesReasoner.removeAxiomAndFlush(query)
    }: @nowarn
  }

  override def dispose(): Unit = {
    acceptedQueriesReasoner.dispose()
  }

}

/* This strategy is described in the KR 2022 paper. */
class BestUserInteraction()(using configuration: RepairConfiguration) extends UserInteraction() {

  private val individuals = configuration.ontologyReasoner.instances(OWLThing)
  private val atomicClassAssertions = individuals.flatMap(individual => configuration.ontologyReasoner.types(individual).filter(_.isAtom).map(atom => individual Type atom))
  private val repairTemplate = mutable.HashSet[Query]()
  private val particularizedRepairRequest = mutable.HashSet.from(configuration.request.axioms)
  private val tboxAxioms = configuration.axioms.filter({ case SubClassOf(_, _, _) => true; case _ => false })
  private val templateReasoner = ELReasoner(tboxAxioms, configuration.subClassExpressions, false)
  private val remainingQueries = mutable.HashSet.from[Query](atomicClassAssertions)

  override protected def initialize(): Unit = {
    computeInheritedAnswers(true)
    remainingQueries.foreach(userInterface.showQuestion)
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    userInterface.removeQuestion(query)
    remainingQueries.remove(query)
    answer match
      case ACCEPT =>
        repairTemplate.add(query)
        templateReasoner.addAxiomAndFlush(query)
      case IGNORE =>
        // Do nothing.
      case DECLINE =>
        particularizedRepairRequest.add(query)
      case _ =>
        ??? // Should never occur.
    computeInheritedAnswers()
  }

  private def computeInheritedAnswers(initialization: Boolean = false): Unit = {
    remainingQueries.foreach(query => {
      if templateReasoner.entails(query) then // inherited accept
        if !initialization then userInterface.removeQuestion(query)
        remainingQueries.remove(query)
      else if {
        templateReasoner.addAxiomAndFlush(query)
        val inheritedDecline = particularizedRepairRequest.exists(templateReasoner.entails)
        templateReasoner.removeAxiomAndFlush(query)
        inheritedDecline
      } then
        if !initialization then userInterface.removeQuestion(query)
        remainingQueries.remove(query)
        particularizedRepairRequest.add(query)
    })
  }

  override def hasBeenCompleted(): Boolean = {
    remainingQueries.isEmpty
  }

  override protected def getRepairSeedUnchecked(): RepairSeed = {
    val seedAxioms = atomicClassAssertions.filter(axiom => (configuration.ontologyReasoner entails axiom) && !(templateReasoner entails axiom))
    RepairSeed(false, seedAxioms: _*)
  }

  override def getButtonTypes(query: Query): collection.Set[Answer] = {
    Set(ACCEPT, IGNORE, DECLINE)
  }

  override def dispose(): Unit = {
    templateReasoner.dispose()
  }

}
