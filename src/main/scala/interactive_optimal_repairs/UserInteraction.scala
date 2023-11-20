package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Answer.*
import interactive_optimal_repairs.RepairType.premises
import interactive_optimal_repairs.Util.ImplicitOWLClassExpression
import protege_components.ProtegeWorker.asynchronouslyInNewWorker

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

object UserInteraction {
  def apply(strategy: Strategy)(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager): UserInteraction =
    strategy match
      case Strategy.FAST => FastUserInteraction()
      case Strategy.BEST => BestUserInteraction()
      case Strategy.FASTSMART => FastSmartUserInteraction()
}

abstract class UserInteraction()(using configuration: RepairConfiguration) {

  var user: User = _
  def start(user: User): Unit = {
    this.user = user
    initialize()
  }

  protected def initialize(): Unit
  def receiveAnswer(query: Query, answer: Answer): Unit
  def hasBeenCompleted(): Boolean
  def getRepairSeed(): RepairSeed
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
            implicitlyAnsweredQueries_Conjunction.foreach { pendingQueries_Conjunction(_).filterNot { subQueriesToBeRetained_Conjunction } foreach { user.removeQuestion } }
            pendingQueries_Conjunction --= implicitlyAnsweredQueries_Conjunction

            val implicitlyAnsweredQueries_ExistentialRestriction =
              pendingQueries_ExistentialRestriction.keySet filter {
                case (_, _, target, filler) => (individual equals target) && (filler isSubsumedBy classExpression wrt configuration.trivialReasoner)
              }
            val diff_ExistentialRestriction = pendingQueries_ExistentialRestriction.keySet diff implicitlyAnsweredQueries_ExistentialRestriction
            val subQueriesToBeRetained_ExistentialRestriction = pendingQueries_ExistentialRestriction.collect({ case (key, (roleAssertion, _)) if diff_ExistentialRestriction contains key => roleAssertion }).toSet[Query]
            implicitlyAnsweredQueries_ExistentialRestriction.foreach { pendingQueries_ExistentialRestriction(_).productIterator.map(_.asInstanceOf[Query]).filterNot { subQueriesToBeRetained_ExistentialRestriction } foreach { user.removeQuestion } }
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
            user.removeQuestion(roleAssertion)
            user.removeQuestion(classAssertion)
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
        pendingQueries_Conjunction(assertion).foreach { user.showQuestion }
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
            user.showQuestion(roleAssertion)
            user.showQuestion(classAssertion)
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
    user.removeQuestion(query)
    answer match
      case Answer.DECLINE => processDeclinedQueries(Iterable.single(query))
      case _ => ??? // Should never occur.
    isCurrentlyProcessing.decrementAndGet()
  }

  override def hasBeenCompleted(): Boolean = {
    isCurrentlyProcessing.get() == 0 && pendingQueries_Conjunction.isEmpty && pendingQueries_ExistentialRestriction.isEmpty
  }

  override def getRepairSeed(): RepairSeed = {
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

class FastSmartUserInteraction()(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends FastUserInteraction() {

  private var phase = 1
  private val pendingPhase2Queries = ConcurrentHashMap.newKeySet[Query]().asScala
  private val declinedPhase2Queries = ConcurrentHashMap.newKeySet[Query]().asScala

  override def start(user: User): Unit = {
    super.start(user)
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
    val seed = getRepairSeed()
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
        user.showQuestion(assertion)
    unsaturatedRepairReasoner.dispose()
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    if (phase equals 2) then
      isCurrentlyProcessing.incrementAndGet()
      pendingPhase2Queries -= query
      user.removeQuestion(query)
      answer match
        case Answer.ACCEPT => // TODO: Should not be ignored in the future!
        case Answer.DECLINE => declinedPhase2Queries += query
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
      Set(ACCEPT, DECLINE)
    else
      Set(DECLINE)
  }

  override def dispose(): Unit = {
    // Do nothing.
  }

}

/* This strategy is described in the KR 2022 paper. */
class BestUserInteraction()(using configuration: RepairConfiguration) extends UserInteraction() {

  val individuals = configuration.ontologyReasoner.instances(OWLThing)
  val atomicClassAssertions = individuals.flatMap(individual => configuration.ontologyReasoner.types(individual).filter(_.isAtom).map(atom => individual Type atom))
  val repairTemplate = mutable.HashSet[Query]()
  val particularizedRepairRequest = mutable.HashSet.from(configuration.request.axioms)
  val tboxAxioms = configuration.axioms.filter({ case SubClassOf(_, _, _) => true; case _ => false })
  val templateReasoner = ELReasoner(tboxAxioms, configuration.subClassExpressions, false)
  val remainingQueries = mutable.HashSet.from[Query](atomicClassAssertions)

  override protected def initialize(): Unit = {
    computeInheritedAnswers(true)
    remainingQueries.foreach(user.showQuestion)
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    user.removeQuestion(query)
    remainingQueries.remove(query)
    answer match
      case Answer.ACCEPT =>
        repairTemplate.add(query)
        templateReasoner.addAxiomAndFlush(query)
      case Answer.DECLINE =>
        particularizedRepairRequest.add(query)
      case Answer.IGNORE =>
        // Do nothing.
    computeInheritedAnswers()
  }

  private def computeInheritedAnswers(initialization: Boolean = false): Unit = {
    remainingQueries.foreach(query => {
      if templateReasoner.entails(query) then // inherited accept
        if !initialization then user.removeQuestion(query)
        remainingQueries.remove(query)
      else if {
        templateReasoner.addAxiomAndFlush(query)
        val inheritedDecline = particularizedRepairRequest.exists(templateReasoner.entails)
        templateReasoner.removeAxiomAndFlush(query)
        inheritedDecline
      } then
        if !initialization then user.removeQuestion(query)
        remainingQueries.remove(query)
        particularizedRepairRequest.add(query)
    })
  }

  override def hasBeenCompleted(): Boolean = {
    remainingQueries.isEmpty
  }

  override def getRepairSeed(): RepairSeed = {
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

enum Strategy(val name: String, val description: String) {
  case FAST extends Strategy("Fast", "Constructs a repair seed with fewest number of questions.")
  case BEST extends Strategy("Best", "Can construct every repair seed.")
  case FASTSMART extends Strategy("Fast-smart", "TBA")
}

trait User {
  def showQuestion(query: Query): Unit
  def removeQuestion(query: Query): Unit
}

enum Answer {
  case ACCEPT, IGNORE, DECLINE
}
