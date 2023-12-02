package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.OWLAPI5CodeConversion.*
import interactive_optimal_repairs.Util.ImplicitOWLClassExpression

import org.phenoscape.scowl.*
//import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLAxiom, OWLClassExpression, OWLObjectPropertyAssertionAxiom, OWLOntologyManager}

//import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*

trait ErrorTolerantReasoner(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) {

  def isBravelyEntailed(queries: collection.Set[Query]): Boolean = {
    // entailmentProbability(queries) > 0f
    queries.forall(configuration.ontologyReasoner.entails) && {
      val subClassExpressions: collection.Set[OWLClassExpression] =
        queries.flatMap(_.nestedClassExpressions().toScala(LazyList)) concat
          configuration.request.axioms.flatMap(_.nestedClassExpressions().toScala(LazyList))
//      // TODO: Implement a variant of ELReasoner that supports multiple ABoxes with a shared TBox.
//      val reasoner = ExtendedClassification(queries ++ configuration.ontology.getTBoxAxioms(Imports.INCLUDED).asScala, subClassExpressions, true)
//      val result = !configuration.request.axioms.exists(reasoner.entails)
//      reasoner.dispose()
//      result
      val aboxIndex = configuration.ontologyReasoner.registerABox(queries.asInstanceOf[collection.Set[OWLAxiom]])
      val result = !configuration.request.axioms.exists(configuration.ontologyReasoner.entails(aboxIndex, _))
      configuration.ontologyReasoner.unregisterABox(aboxIndex)
      result
    }
  }

  def isCautiouslyEntailed(queries: collection.Set[Query]): Boolean = {
    entailmentProbability(queries) == 1f
  }

  def entailmentProbability(queries: collection.Set[Query]): Float

}

class ErrorTolerantIQReasoner(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends ErrorTolerantReasoner() {

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

class ErrorTolerantIRQReasoner(using configuration: RepairConfiguration, ontologyManager: OWLOntologyManager) extends ErrorTolerantReasoner() {

  def entailmentProbability(queries: collection.Set[Query]): Float = {
    ???
  }

}

