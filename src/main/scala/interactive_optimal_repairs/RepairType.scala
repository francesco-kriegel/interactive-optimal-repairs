package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.RepairType.premises
import interactive_optimal_repairs.Util.{CoverageReasonerRequest, ImplicitIterableOfOWLClassExpressions, ImplicitOWLClassExpression, maximalElements, minimalElements}

import org.phenoscape.scowl.*
import org.semanticweb.owlapi.model.OWLClassExpression

import scala.collection
import scala.collection.{immutable, mutable}
import scala.jdk.CollectionConverters.*
import scala.util.hashing.MurmurHash3

class RepairType(val node: IQSaturationNode, val atoms: Set[OWLClassExpression])(using configuration: RepairConfiguration) {

  private lazy val types =
    node match
      case KernelObject(individual) => Set.from(configuration.classificationOfInputOntology.types(individual))
      case ShellObject(classExpression) => Set.from(configuration.classificationOfInputOntology.subsumers(classExpression))

  lazy val isRepairType: Boolean = {
    (atoms subsetOf types)
      && atoms.forall(_.isAtom)
      && atoms.forall(c => !atoms.exists(d => (c ne d) && (c isSubsumedBy d wrt configuration.classificationOfEmptyOntology)))
      && atoms.forall(premises(node, _) isCoveredBy atoms wrt configuration.classificationOfEmptyOntology)
  }

  private def lowering(atomsToBeNotCovered: collection.Set[OWLClassExpression]): Set[OWLClassExpression] = {
    if !(atomsToBeNotCovered isCoveredBy atoms wrt configuration.classificationOfEmptyOntology) then throw IllegalArgumentException() // this could also be returned
    maximalElements(
      types
        .filter(c => c.isAtom
          && atoms.exists(c isSubsumedBy _ wrt configuration.classificationOfEmptyOntology)
          && !atomsToBeNotCovered.exists(_ isSubsumedBy c wrt configuration.classificationOfEmptyOntology)),
      configuration.classificationOfEmptyOntology.lteq)
  }

  def lowering(atom: OWLClassExpression): RepairType = {
    if !(atoms contains atom) then throw IllegalArgumentException()
    val atomsToBeNotCovered = mutable.HashSet(atom)
    var low = lowering(atomsToBeNotCovered)
    var notDone = true
    while (notDone) {
      val newAtomsToBeNotCovered =
        low.filterNot(premises(node, _) isCoveredBy low wrt configuration.classificationOfEmptyOntology)
      atomsToBeNotCovered.addAll(newAtomsToBeNotCovered)
      low = lowering(atomsToBeNotCovered)
      notDone = newAtomsToBeNotCovered.nonEmpty
    }
    RepairType(node, low)
  }

  def isMinimalRepairTypeCovering(classExpressionsToBeCovered: collection.Set[OWLClassExpression]): Boolean = {
    isRepairType
      && (classExpressionsToBeCovered isCoveredBy atoms wrt configuration.classificationOfEmptyOntology)
      && !atoms.exists(classExpressionsToBeCovered isCoveredBy lowering(_) wrt configuration.classificationOfEmptyOntology)
  }

  def errorCode(classExpressionsToBeCovered: collection.Set[OWLClassExpression]): Int = {
    var result = 0
    if !(atoms subsetOf types) then result += 1 << 0
    if !atoms.forall(_.isAtom) then result += 1 << 1
    if atoms.exists(c => atoms.exists(d => (c ne d) && (c isSubsumedBy d wrt configuration.classificationOfEmptyOntology))) then result += 1 << 2
    if !atoms.forall(premises(node, _) isCoveredBy atoms wrt configuration.classificationOfEmptyOntology) then result += 1 << 3
    if !(classExpressionsToBeCovered isCoveredBy atoms wrt configuration.classificationOfEmptyOntology) then result += 1 << 4
    if atoms.exists(classExpressionsToBeCovered isCoveredBy lowering(_) wrt configuration.classificationOfEmptyOntology) then result += 1 << 5
    result
  }

  def isCoveredBy(others: RepairType): CoverageReasonerRequest =
    CoverageReasonerRequest(atoms, others.atoms, false)

  def isStrictlyCoveredBy(others: RepairType): CoverageReasonerRequest =
    CoverageReasonerRequest(atoms, others.atoms, true)

  override def equals(that: Any): Boolean = {
    that match
      case that: RepairType => (this.node equals that.node) && (this.atoms equals that.atoms)
      case _ => false
  }

  override def hashCode(): Int = {
    MurmurHash3.productHash((this.node.hashCode(), MurmurHash3.unorderedHash(this.atoms)))
  }

  override def toString: String = {
    atoms.map(_.toShortDLString).mkString("RepairType( " + node + " | ", " , ", " )")
  }

}

object RepairType {

  private def atoms(classExpressions: collection.Set[OWLClassExpression]): collection.Set[OWLClassExpression] =
    classExpressions.filter(_.isAtom)

  private def uncoveredConjunctions(classExpressions: collection.Set[OWLClassExpression])(using configuration: RepairConfiguration): collection.Set[OWLClassExpression] = {
    classExpressions.filter(c => !c.isAtom && !atoms(classExpressions).exists(c isSubsumedBy _ wrt configuration.classificationOfEmptyOntology))
//    classExpressions.filter(c => !classExpressions.exists(c isSubsumedBy _ wrt configuration.trivialReasoner))
  }

  def premises(node: IQSaturationNode, atom: OWLClassExpression)(using configuration: RepairConfiguration): collection.Set[OWLClassExpression] = {
    val isSubsumedByAtom = configuration.classificationOfInputOntology.subsumees(atom).toSet
    node match
      case KernelObject(individual) =>
        configuration.classificationOfInputOntology.types(individual).filter({ configuration.conceptInclusionsMap.getOrElse(_, Set.empty) exists isSubsumedByAtom }).toSet
      case ShellObject(classExpression) =>
        configuration.classificationOfInputOntology.subsumers(classExpression).filter({ configuration.conceptInclusionsMap.getOrElse(_, Set.empty) exists isSubsumedByAtom }).toSet
  }

//  @Deprecated // Does not always return a minimal repair type!
//  private def computeOneMinimalRepairType(individual: OWLIndividual, classExpressionsToBeCovered: collection.Set[OWLClassExpression])(using configuration: RepairConfiguration): Option[RepairType] = {
//    val types = Set.from(configuration.ontologyReasoner.types(individual))
//    if !(classExpressionsToBeCovered subsetOf types) then throw IllegalArgumentException() // sanity check, could be removed
//    val filteredClassExpressionsToBeCovered = classExpressionsToBeCovered.filter(types.contains)
//    var preType = filteredClassExpressionsToBeCovered ++ filteredClassExpressionsToBeCovered.flatMap(configuration.ontologyReasoner.premisesAmongSubsumers).filter(types.contains)
//    var notDone = true
//    var notNone = true
//    while (notDone && notNone)
//      val uc = uncoveredConjunctions(preType)
//      notDone = uc.nonEmpty
//      if notDone then
//        val tlc = Random.shuffle(uc.flatMap(_.topLevelConjuncts()))
//        val nextPreType =
//          tlc.map(atom =>
//              preType ++ Set(atom) ++ configuration.ontologyReasoner.premisesAmongSubsumers(atom).filter(types.contains))
//            .find(nextPreType =>
//              !tlc.exists(btom => (atoms(preType ++ Set(btom) ++ configuration.ontologyReasoner.premisesAmongSubsumers(btom).filter(types.contains)) isStrictlyCoveredBy atoms(nextPreType) wrt configuration.trivialReasoner)))
//        notNone = nextPreType.isDefined && !(nextPreType.get contains OWLThing)
//        if notNone then
//          preType = nextPreType.get
//    if notNone then Some(RepairType(individual, collection.immutable.Set.from(maximalElements(atoms(preType), _ isSubsumedBy _ wrt configuration.trivialReasoner)))) else None
//  }

  def computeAllMinimalRepairTypes(node: IQSaturationNode, classExpressionsToBeCovered: collection.Set[OWLClassExpression])(using configuration: RepairConfiguration): collection.Set[RepairType] = {
    val types =
      node match
        case KernelObject(individual) => Set.from(configuration.classificationOfInputOntology.types(individual))
        case ShellObject(classExpression) => Set.from(configuration.classificationOfInputOntology.subsumers(classExpression))
    if !(classExpressionsToBeCovered subsetOf types) then
      Console.err.println("Individual: " + node)
      Console.err.println("To be covered: " + classExpressionsToBeCovered)
      Console.err.println("Types: " + types)
      throw IllegalArgumentException() // sanity check, could be removed
    val filteredClassExpressionsToBeCovered = classExpressionsToBeCovered intersect types
    var preTypes = mutable.HashSet(
      filteredClassExpressionsToBeCovered ++ filteredClassExpressionsToBeCovered.flatMap(premises(node, _)))
    val minTypes = mutable.HashSet[collection.Set[OWLClassExpression]]()
    while (preTypes.nonEmpty)
      val nextPreTypes = mutable.HashSet[collection.Set[OWLClassExpression]]()
      for (preType <- preTypes)
        val uc = uncoveredConjunctions(preType)
        if uc.nonEmpty then
          val tlc = uc.flatMap(_.topLevelConjuncts())//.toList.sortWith((atom, btom) => uc.filter(_.topLevelConjuncts() contains atom).size > uc.filter(_.topLevelConjuncts() contains btom).size)
          tlc.map(atom =>
              preType ++ Set(atom) ++ premises(node, atom))
            .filter(nextPreType =>
              !tlc.exists(btom => atoms(preType ++ Set(btom) ++ premises(node, btom)) isStrictlyCoveredBy atoms(nextPreType) wrt configuration.classificationOfEmptyOntology))
            .foreach(nextPreType =>
              nextPreTypes.add(nextPreType))
        else
          minTypes.add(maximalElements(atoms(preType), _ isSubsumedBy _ wrt configuration.classificationOfEmptyOntology))
      preTypes = nextPreTypes.filterNot(_ contains OWLThing)
    minimalElements(minTypes, _ isCoveredBy _ wrt configuration.classificationOfEmptyOntology).map(mintype => RepairType(node, collection.immutable.Set.from(mintype)))
  }

}
