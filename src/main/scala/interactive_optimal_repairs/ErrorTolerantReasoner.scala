package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*
import interactive_optimal_repairs.Util.ImplicitOWLClassExpression

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLObjectPropertyAssertionAxiom}

import scala.jdk.StreamConverters.*

trait ErrorTolerantReasoner(using configuration: RepairConfiguration) {

  def isBravelyEntailed(queries: collection.Set[Query]): Boolean = {
    // entailmentProbability(queries) > 0f
    queries.forall(configuration.ontologyReasoner.entails) && {
      val subClassExpressions: collection.Set[OWLClassExpression] =
        queries.flatMap(_.nestedClassExpressions().toScala(LazyList)) concat
          configuration.request.axioms.flatMap(_.nestedClassExpressions().toScala(LazyList))
      val reasoner: ELReasoner = ELReasoner(queries, subClassExpressions, true)
      !configuration.request.axioms.exists(reasoner.entails)
    }
  }

  def isCautiouslyEntailed(queries: collection.Set[Query]): Boolean = {
    entailmentProbability(queries) == 1f
  }

  def entailmentProbability(queries: collection.Set[Query]): Float

}

class ErrorTolerantIQReasoner(using configuration: RepairConfiguration) extends ErrorTolerantReasoner() {

  def entailmentProbability(queries: collection.Set[Query]): Float = {
    if queries.exists({
      case _: OWLObjectPropertyAssertionAxiom => true
      case ClassAssertion(_, classExpression, individual) => !ELExpressivityChecker.checkClassExpression(classExpression) || individual.isAnonymous
      case _ => true
    }) then
      throw IllegalArgumentException("The supplied query set contains a query not in IQ.")
    else
      if queries.forall {
        case classAssertion@ClassAssertion(_, _, _) => configuration.ontologyReasoner entails classAssertion
        case _ => false
      } then
        val individuals = queries.collect { case ClassAssertion(_, _, individual) => individual.asOWLNamedIndividual() }
        individuals.map { individual =>
          val minimalRepairTypes = RepairType.computeAllMinimalRepairTypes(individual, configuration.request.getClassExpressions(individual))
          val denominator = minimalRepairTypes.size
          val numerator = minimalRepairTypes.count { repairType =>
            queries.forall {
              case ClassAssertion(_, classExpression, jndividual)
                if individual equals jndividual =>
                  !(classExpression isCoveredBy repairType wrt configuration.ontologyReasoner)
              case _ => true
            }
          }
          numerator.toFloat / denominator.toFloat
        }.fold(1f) { _ * _ }
      else
        0f
  }

}

class ErrorTolerantIRQReasoner(using configuration: RepairConfiguration) extends ErrorTolerantReasoner() {

  def entailmentProbability(queries: collection.Set[Query]): Float = {
    ???
  }

}

