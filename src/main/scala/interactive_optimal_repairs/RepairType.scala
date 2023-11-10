package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Util.{CoverageReasonerRequest, ImplicitIterableOfOWLClassExpressions, ImplicitOWLClassExpression, maximalElements, minimalElements}

import org.phenoscape.scowl.OWLThing
import org.semanticweb.owlapi.model.{OWLClassExpression, OWLIndividual}

import scala.collection
import scala.collection.{immutable, mutable}
import scala.util.hashing.MurmurHash3

class RepairType(val node: IQSaturationNode, val atoms: Set[OWLClassExpression])(using configuration: RepairConfiguration) {

  private lazy val types =
    node match
      case individual: OWLIndividual => Set.from(configuration.ontologyReasoner.types(individual))
      case classExpression: OWLClassExpression => Set.from(configuration.ontologyReasoner.subsumers(classExpression))

  lazy val isRepairType: Boolean = {
    (atoms subsetOf types)
      && atoms.forall(_.isAtom)
      && atoms.forall(c => !atoms.exists(d => (c ne d) && (c isSubsumedBy d wrt configuration.trivialReasoner)))
      && atoms.forall(configuration.ontologyReasoner.premisesAmongSubsumers(_).filter(types.contains) isCoveredBy atoms wrt configuration.trivialReasoner)
  }

  private def lowering(atomsToBeNotCovered: collection.Set[OWLClassExpression]): Set[OWLClassExpression] = {
    if !(atomsToBeNotCovered isCoveredBy atoms wrt configuration.trivialReasoner) then throw IllegalArgumentException() // this could also be returned
    maximalElements(
      types
        .filter(c => c.isAtom
          && atoms.exists(c isSubsumedBy _ wrt configuration.trivialReasoner)
          && !atomsToBeNotCovered.exists(_ isSubsumedBy c wrt configuration.trivialReasoner)),
      configuration.trivialReasoner.lteq)
  }

  def lowering(atom: OWLClassExpression): RepairType = {
    if !(atoms contains atom) then throw IllegalArgumentException()
    val atomsToBeNotCovered = mutable.HashSet(atom)
    var low = lowering(atomsToBeNotCovered)
    var notDone = true
    while (notDone) {
      val newAtomsToBeNotCovered =
        low.filterNot(configuration.ontologyReasoner.premisesAmongSubsumers(_).filter(types.contains) isCoveredBy low wrt configuration.trivialReasoner)
      atomsToBeNotCovered.addAll(newAtomsToBeNotCovered)
      low = lowering(atomsToBeNotCovered)
      notDone = newAtomsToBeNotCovered.nonEmpty
    }
    RepairType(node, low)
  }

  def isMinimalRepairTypeCovering(classExpressionsToBeCovered: collection.Set[OWLClassExpression]): Boolean = {
    isRepairType
      && (classExpressionsToBeCovered isCoveredBy atoms wrt configuration.trivialReasoner)
      && !atoms.exists(classExpressionsToBeCovered isCoveredBy lowering(_) wrt configuration.trivialReasoner)
  }

  def errorCode(classExpressionsToBeCovered: collection.Set[OWLClassExpression]): Int = {
    var result = 0
    if !(atoms subsetOf types) then result += 1 << 0
    if !atoms.forall(_.isAtom) then result += 1 << 1
    if !atoms.forall(c => !atoms.exists(d => (c ne d) && (c isSubsumedBy d wrt configuration.trivialReasoner))) then result += 1 << 2
    if !atoms.forall(configuration.ontologyReasoner.premisesAmongSubsumers(_).filter(types.contains) isCoveredBy atoms wrt configuration.trivialReasoner) then result += 1 << 3
    if !(classExpressionsToBeCovered isCoveredBy atoms wrt configuration.trivialReasoner) then result += 1 << 4
    if atoms.exists(classExpressionsToBeCovered isCoveredBy lowering(_) wrt configuration.trivialReasoner) then result += 1 << 5
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

object RepairTypes {

  private def atoms(classExpressions: collection.Set[OWLClassExpression]): collection.Set[OWLClassExpression] =
    classExpressions.filter(_.isAtom)

  private def uncoveredConjunctions(classExpressions: collection.Set[OWLClassExpression])(using configuration: RepairConfiguration): collection.Set[OWLClassExpression] = {
    classExpressions.filter(c => !c.isAtom && !atoms(classExpressions).exists(c isSubsumedBy _ wrt configuration.trivialReasoner))
//    classExpressions.filter(c => !classExpressions.exists(c isSubsumedBy _ wrt configuration.trivialReasoner))
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

  def computeAllMinimalRepairTypes(individual: IQSaturationNode, classExpressionsToBeCovered: collection.Set[OWLClassExpression])(using configuration: RepairConfiguration): collection.Set[RepairType] = {
    val types =
      individual match
        case individual: OWLIndividual => Set.from(configuration.ontologyReasoner.types(individual))
        case classExpression: OWLClassExpression => Set.from(configuration.ontologyReasoner.subsumers(classExpression))
    if !(classExpressionsToBeCovered subsetOf types) then
      Console.err.println("Individual: " + individual)
      Console.err.println("To be covered: " + classExpressionsToBeCovered)
      Console.err.println("Types: " + types)
      throw IllegalArgumentException() // sanity check, could be removed
    val filteredClassExpressionsToBeCovered = classExpressionsToBeCovered.filter(types.contains)
    var preTypes = mutable.HashSet(
      filteredClassExpressionsToBeCovered ++ filteredClassExpressionsToBeCovered.flatMap(configuration.ontologyReasoner.premisesAmongSubsumers).filter(types.contains))
    val minTypes = mutable.HashSet[collection.Set[OWLClassExpression]]()
    while (preTypes.nonEmpty)
      val nextPreTypes = mutable.HashSet[collection.Set[OWLClassExpression]]()
      for (preType <- preTypes)
        val uc = uncoveredConjunctions(preType)
        if uc.nonEmpty then
          val tlc = uc.flatMap(_.topLevelConjuncts())//.toList.sortWith((atom, btom) => uc.filter(_.topLevelConjuncts() contains atom).size > uc.filter(_.topLevelConjuncts() contains btom).size)
          tlc.map(atom =>
              preType ++ Set(atom) ++ configuration.ontologyReasoner.premisesAmongSubsumers(atom).filter(types.contains))
            .filter(nextPreType =>
              !tlc.exists(btom => (atoms(preType ++ Set(btom) ++ configuration.ontologyReasoner.premisesAmongSubsumers(btom).filter(types.contains)) isStrictlyCoveredBy atoms(nextPreType) wrt configuration.trivialReasoner)))
            .foreach(nextPreType =>
              nextPreTypes.add(nextPreType))
        else
          minTypes.add(maximalElements(atoms(preType), _ isSubsumedBy _ wrt configuration.trivialReasoner))
      preTypes = nextPreTypes.filterNot(_ contains OWLThing)
    minimalElements(minTypes, _ isCoveredBy _ wrt configuration.trivialReasoner).map(mintype => RepairType(individual, collection.immutable.Set.from(mintype)))
  }

}
