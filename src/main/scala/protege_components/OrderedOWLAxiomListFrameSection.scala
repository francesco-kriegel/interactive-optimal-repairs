package de.tu_dresden.inf.lat
package protege_components

import protege_components.Util.*

import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.editor.OWLObjectEditor
import org.protege.editor.owl.ui.frame.{AbstractOWLFrameSection, OWLFrameSectionRow}
import org.semanticweb.owlapi.model.{OWLAxiom, OWLOntology, OWLOntologyChange}

import java.util
import java.util.{Comparator, Set}

private class OrderedOWLAxiomListFrameSection[Ax <: OWLAxiom](sectionLabel: String, rowLabel: String, owlFrame: OrderedOWLAxiomListFrame[Ax], rowComparator: Comparator[OrderedOWLAxiomListFrameSectionRow[Ax]])(using owlEditorKit: OWLEditorKit)
  extends AbstractOWLFrameSection[util.Set[Ax], Ax, Ax](owlEditorKit, sectionLabel, rowLabel, owlFrame) {

//  private val rowComparator = new DefaultRowComparator
//  private val added = new util.HashSet[Ax]

  override protected def createAxiom(ax: Ax): Ax = ax

  override def getObjectEditor: OWLObjectEditor[Ax] = null

  override protected def refill(ontology: OWLOntology): Unit = {
//    val axs = this.getRootObject.asInstanceOf[util.Set[_]]
//    val var3 = axs.iterator
//    while (var3.hasNext) {
//      val ax = var3.next.asInstanceOf[Ax]
//      if (ontology.containsAxiom(ax)) {
//        this.addRow(OrderedOWLAxiomListFrameSectionRow(this.getOWLEditorKit, this, ontology, this.getRootObject.asInstanceOf[util.Set[Ax]], ax))
//        this.added.add(ax)
//      }
//    }
  }

  override protected def refillInferred(): Unit = {
//    val axs = this.getRootObject.asInstanceOf[util.Set[_]]
//    val var2 = axs.iterator
//    while (var2.hasNext) {
//      val ax = var2.next.asInstanceOf[Ax]
//      if (!this.added.contains(ax)) this.addRow(OrderedOWLAxiomListFrameSectionRow(this.getOWLEditorKit, this, null.asInstanceOf[OWLOntology], this.getRootObject.asInstanceOf[util.Set[Ax]], ax))
//    }
    val axioms = this.getRootObject
    axioms.forEach(ax =>
      this.addRow(OrderedOWLAxiomListFrameSectionRow(ax, this, axioms)))
  }

  override protected def clear(): Unit = {
//    this.added.clear()
  }

  override def getRowComparator: Comparator[OWLFrameSectionRow[util.Set[Ax], Ax, Ax]] = rowComparator.asInstanceOf[Comparator[OWLFrameSectionRow[util.Set[Ax], Ax, Ax]]]

  override def canAdd = true

  override protected def isResettingChange(change: OWLOntologyChange): Boolean = change.isAxiomChange

//  private class DefaultRowComparator extends Comparator[OWLFrameSectionRow[util.Set[Ax], Ax, Ax]] {
//    private val objComparator = OrderedOWLAxiomListFrameSection.this.getOWLModelManager.getOWLObjectComparator
//    override def compare(o1: OWLFrameSectionRow[util.Set[Ax], Ax, Ax], o2: OWLFrameSectionRow[util.Set[Ax], Ax, Ax]): Int = this.objComparator.compare(o1.getAxiom, o2.getAxiom)
//  }

}
