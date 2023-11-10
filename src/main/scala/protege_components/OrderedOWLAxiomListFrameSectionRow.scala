package de.tu_dresden.inf.lat
package protege_components

import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.editor.OWLObjectEditor
import org.protege.editor.owl.ui.frame.AbstractOWLFrameSectionRow
import org.semanticweb.owlapi.model.{OWLAxiom, OWLOntology}

import java.util
import java.util.{Arrays, List, Set}

class OrderedOWLAxiomListFrameSectionRow[Ax <: OWLAxiom](axiom: Ax, section: OrderedOWLAxiomListFrameSection[Ax], rootObject: util.Set[Ax])(using owlEditorKit: OWLEditorKit)
  extends AbstractOWLFrameSectionRow[util.Set[Ax], Ax, Ax](owlEditorKit, section, null.asInstanceOf[OWLOntology], rootObject, axiom) {

  override protected def getObjectEditor: OWLObjectEditor[Ax] = null

  override protected def createAxiom(editedObject: Ax): Ax = editedObject

  override def getManipulatableObjects: util.List[Ax] = util.Arrays.asList(this.getAxiom)

  override def isEditable = true

  override def isDeleteable = true

  override def handleEditingFinished(editedObjects: util.Set[Ax]): Unit = {}

  override def getTooltip: String = "TBA"

  override def isInferred: Boolean = false

}
