package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.RepairType.premises
import interactive_optimal_repairs.Util.ImplicitOWLClassExpression

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLClassExpression, OWLIndividual, OWLNamedIndividual, OWLObjectProperty, OWLObjectPropertyAssertionAxiom}

import java.util.concurrent.atomic.AtomicInteger
import scala.annotation.tailrec
import scala.collection.mutable

object UserInteraction {
  def apply(strategy: Strategy)(using configuration: RepairConfiguration): UserInteraction =
    strategy match
      case Strategy.FAST => FastUserInteraction()
      case Strategy.BEST => BestUserInteraction()
      case Strategy.SMART => SmartUserInteraction()
}

abstract class UserInteraction()(using configuration: RepairConfiguration) {

  var user: User = _
  def start(user: User): Unit = {
    this.user = user
    start()
  }

  protected def start(): Unit
  def receiveAnswer(query: Query, answer: Answer): Unit
  def hasBeenCompleted(): Boolean
  def getRepairSeed(): RepairSeed

}

/* This strategy is described in the JELIA 2023 paper. */
class FastUserInteraction()(using configuration: RepairConfiguration) extends UserInteraction() {

  private val repairSeed = mutable.HashMap[OWLNamedIndividual, mutable.HashSet[OWLClassExpression]]()
  private val nonDeclinedRoleAssertions = mutable.HashSet[OWLObjectPropertyAssertionAxiom]()
  private val pendingQueries_Conjunction = mutable.HashMap[OWLClassAssertionAxiom, mutable.HashSet[OWLClassAssertionAxiom]]()
              // contains entries a:C₁⊓...⊓Cₙ ⟼ a:C₁ | ... | a:Cₙ
  private val pendingQueries_ExistentialRestriction = mutable.HashMap[(OWLIndividual, OWLObjectProperty, OWLIndividual, OWLClassExpression), (OWLObjectPropertyAssertionAxiom, OWLClassAssertionAxiom)]()
              // contains entries (a,r,b,C) ⟼ (a,b):r | b:C
  private val isCurrentlyProcessing = AtomicInteger(0)

  private def processDeclinedQueries(queries: Iterable[Query]): Unit = {
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

  override protected def start(): Unit = {
    configuration.axioms.foreach {
      case roleAssertion: OWLObjectPropertyAssertionAxiom => nonDeclinedRoleAssertions += roleAssertion
      case _ => // Do nothing.
    }
    processDeclinedQueries(configuration.request.axioms.filter { configuration.ontologyReasoner.entails })
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    isCurrentlyProcessing.incrementAndGet()
    user.removeQuestion(query)
    // query match
    //   case query: OWLClassAssertionAxiom =>
    //     pendingQueries_Conjunction -= query
    //   case query: OWLObjectPropertyAssertionAxiom =>
    //     // TODO
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

}

class SmartUserInteraction()(using configuration: RepairConfiguration) extends UserInteraction() {

  //      case Strategy.SMART =>
  //        // We should only consider the environments of individuals in the repair request,
  //        // as well as the individuals reachable on a path of accepted role assertions.  Any ideas?
  //        throw NotImplementedError()

  override protected def start(): Unit = ???

  override def receiveAnswer(query: Query, answer: Answer): Unit = ???

  override def hasBeenCompleted(): Boolean = ???

  override def getRepairSeed(): RepairSeed = ???

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

  override protected def start(): Unit = {
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

}

enum Strategy {
  case FAST, BEST, SMART
}

trait User {
  def showQuestion(query: Query): Unit
  def removeQuestion(query: Query): Unit
}

enum Answer {
  case ACCEPT, DECLINE, IGNORE
}
