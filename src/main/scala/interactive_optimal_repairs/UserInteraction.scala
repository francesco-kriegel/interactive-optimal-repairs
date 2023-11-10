package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Util.ImplicitOWLClassExpression

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLClassExpression, OWLNamedIndividual}

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

//  val individuals = configuration.ontologyReasoner.instances(OWLThing)
//
//  val types = mutable.HashMap[OWLNamedIndividual, collection.Set[OWLClassExpression]]()
//  def getTypes(individual: OWLNamedIndividual): collection.Set[OWLClassExpression] =
//    types.getOrElseUpdate(individual, { configuration.ontologyReasoner.types(individual).toSet })
//
//  val preservedRoleAssertions = mutable.HashSet[OWLObjectPropertyAssertionAxiom]()
//  configuration.axioms.foreach({ case 𝛂 @ ObjectPropertyAssertion(_, _, _: OWLNamedIndividual, _: OWLNamedIndividual) => preservedRoleAssertions.add(𝛂); case _ => {} })
//
//  val forbiddenTypesInTheRepair = mutable.HashMap[OWLNamedIndividual, mutable.HashSet[OWLClassExpression]]()
//  def addForbiddenType(individual: OWLNamedIndividual, classExpression: OWLClassExpression): Unit =
//    forbiddenTypesInTheRepair.getOrElseUpdate(individual, { mutable.HashSet[OWLClassExpression]() }).add(classExpression)
//  def addForbiddenTypes(individual: OWLNamedIndividual, classExpressions: Iterable[OWLClassExpression]): Unit =
//    forbiddenTypesInTheRepair.getOrElseUpdate(individual, { mutable.HashSet[OWLClassExpression]() }).addAll(classExpressions)
//  individuals.foreach { individual =>
//    addForbiddenTypes(individual, configuration.repairRequest.getClassExpressions(individual) intersect getTypes(individual))
//  }
//
//  // construct sets of questions, of which the user must decline at least (accepting all would be an error).
//  // for an undecided conjunction C for individual a, take all assertions D(a) where D is tlc of C
//  // for an existential restriction ∃r.C for individual a and an undecided role assertion r(a,b), take the assertions r(a,b) and C(b)
//
//  forbiddenTypesInTheRepair.flatMap((individual, classExpressions) => classExpressions.map((individual, _)))
//    .filter { (individual, classExpression) =>
//      !classExpression.isAtom && !(classExpression isCoveredBy forbiddenTypesInTheRepair(individual).filter(_.isAtom) wrt configuration.trivialReasoner)
//    }
//
//  preservedRoleAssertions.flatMap {
//    case ObjectPropertyAssertion(_, property, subject: OWLNamedIndividual, target: OWLNamedIndividual) =>
//      forbiddenTypesInTheRepair(subject) collectFirst {
//          case ObjectSomeValuesFrom(qroperty, classExpression) if (property equals qroperty) && !(classExpression isCoveredBy forbiddenTypesInTheRepair(target).filter(_.isAtom) wrt configuration.trivialReasoner)
//            => (property, subject, target, classExpression)
//        }
//  }
//
  private val _repairSeed = mutable.HashMap[OWLNamedIndividual, mutable.HashSet[OWLClassExpression]]()
  private val pendingQueries = mutable.HashMap[Query, mutable.HashSet[Query]]()
  private val isCurrentlyProcessing = AtomicInteger(0)

  private def processDeclinedQueries(queries: Iterable[Query]): Unit = {
    val undecidedQueries = mutable.HashSet[Query]()
    @tailrec def recursivelyProcess(qs: Iterable[Query]): Unit = {
      val ps = mutable.HashSet[Query]()
      qs.foreach {
        case ass @ ClassAssertion(_, classExpression, individual) =>
          if classExpression.isAtom then
            _repairSeed.getOrElseUpdate(individual.asOWLNamedIndividual(), { mutable.HashSet[OWLClassExpression]() }).add(classExpression)
            val implicitlyAnsweredQueries =
              pendingQueries.keySet filter {
                case ClassAssertion(_, dlassExpression, jndividual) =>
                  (individual eq jndividual) && (dlassExpression isSubsumedBy classExpression wrt configuration.trivialReasoner)
                case _ => ???
              }
            val diff = pendingQueries.keySet diff implicitlyAnsweredQueries
            val subQueriesToBeRetained = pendingQueries.flatMap((query, subQueries) => if diff contains query then subQueries else collection.Set.empty).toSet
            implicitlyAnsweredQueries.foreach { pendingQueries(_).filterNot { subQueriesToBeRetained } foreach { user.removeQuestion } }
            pendingQueries --= implicitlyAnsweredQueries
            val premises =
              (configuration.ontologyReasoner.premisesAmongSubsumees(classExpression)
                intersect configuration.ontologyReasoner.types(individual)
                filterNot { _ isCoveredBy _repairSeed.getOrElse(individual.asOWLNamedIndividual(), { mutable.HashSet.empty }) wrt configuration.trivialReasoner }
              ).toSet
            ps ++= premises.map(individual Type _)
          else
            undecidedQueries += ass
        case _ => // Do nothing.
      }
      if ps.nonEmpty then recursivelyProcess(ps)
    }
    recursivelyProcess(queries)
    undecidedQueries --= pendingQueries.keySet
    undecidedQueries.filterInPlace {
      case ClassAssertion(_, classExpression, individual) =>
        !(classExpression isCoveredBy _repairSeed.getOrElse(individual.asOWLNamedIndividual(), { mutable.HashSet.empty }) wrt configuration.trivialReasoner)
      case _ => ???
    }
    undecidedQueries.foreach {
      case ass @ ClassAssertion(_, classExpression, individual) =>
        pendingQueries(ass) = mutable.HashSet[Query]()
        classExpression.topLevelConjuncts().foreach { atom => pendingQueries(ass) += (individual Type atom) }
        pendingQueries(ass).foreach { user.showQuestion }
      case _ => ???
    }
  }

  override protected def start(): Unit = {
    processDeclinedQueries(configuration.repairRequest.axioms.filter { configuration.ontologyReasoner.entails })
  }

  override def receiveAnswer(query: Query, answer: Answer): Unit = {
    isCurrentlyProcessing.incrementAndGet()
    user.removeQuestion(query)
    pendingQueries -= query
    answer match
      case Answer.DECLINE => processDeclinedQueries(Iterable.single(query))
      case _ => ??? // Should never occur.
    isCurrentlyProcessing.decrementAndGet()
  }

  override def hasBeenCompleted(): Boolean = {
    isCurrentlyProcessing.get() == 0 && pendingQueries.isEmpty
  }

  override def getRepairSeed(): RepairSeed = {
    val axioms = _repairSeed.flatMap((individual, atoms) => atoms.map(atom => individual Type atom))
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
  val particularizedRepairRequest = mutable.HashSet.from(configuration.repairRequest.axioms)
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
