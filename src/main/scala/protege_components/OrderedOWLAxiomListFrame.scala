package de.tu_dresden.inf.lat
package protege_components

import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.ui.frame.AbstractOWLFrame
import org.semanticweb.owlapi.model.OWLAxiom

import java.util
import java.util.Set

private class OrderedOWLAxiomListFrame[Ax <: OWLAxiom](using owlEditorKit: OWLEditorKit)
  extends AbstractOWLFrame[java.util.Set[Ax]](owlEditorKit.getModelManager.getOWLOntologyManager) {

  def addSection(section: OrderedOWLAxiomListFrameSection[Ax]): Unit = super.addSection(section)

}
