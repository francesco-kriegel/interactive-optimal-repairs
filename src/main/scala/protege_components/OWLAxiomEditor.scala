package de.tu_dresden.inf.lat
package protege_components

import protege_components.Util.*

import org.protege.editor.core.ui.util.{InputVerificationStatusChangedListener, VerifiedInputEditor}
import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.model.classexpression.OWLExpressionParserException
import org.protege.editor.owl.ui.clsdescriptioneditor.ExpressionEditor
import org.protege.editor.owl.ui.editor.AbstractOWLObjectEditor
import org.semanticweb.owlapi.model.{OWLAxiom, OWLObjectPropertyAssertionAxiom}

import java.awt.*
import java.util.Collections
import javax.annotation.Nonnull
import javax.swing.*
import javax.swing.event.DocumentListener
import scala.reflect.{ClassTag, classTag}

class OWLAxiomEditor[Ax <: OWLAxiom : ClassTag](private val editorKit: OWLEditorKit, unexpectedAxiomException: () => OWLExpressionParserException = () => OWLExpressionParserException("Expected an OWL axiom", 0, 0, false, false, false, false, false, false, Collections.emptySet)) extends AbstractOWLObjectEditor[Ax] with VerifiedInputEditor {

  private val editor: ExpressionEditor[Ax] = ExpressionEditor[Ax](editorKit, OWLAxiomChecker[Ax](editorKit.getModelManager, unexpectedAxiomException))
  this.editor.setText(" ")
  private val editingComponent: JComponent = JPanel(BorderLayout())
  this.editingComponent.add(this.editor)
  this.editingComponent.setPreferredSize(Dimension(400, 200))

  override def setEditedObject(axiom: Ax): Boolean = {
    if (axiom == null) editor.setText("")
    else
      val rendering =
        if axiom.isInstanceOf[OWLObjectPropertyAssertionAxiom] then
          val spo = axiom.asInstanceOf[OWLObjectPropertyAssertionAxiom]
          editorKit.getModelManager.getRendering(spo.getSubject)
            + " Fact: " + editorKit.getModelManager.getRendering(spo.getProperty)
            + " " + editorKit.getModelManager.getRendering(spo.getObject)
        else
          editorKit.getModelManager.getRendering(axiom)
            .replaceFirst("Type", "Type:")
            .replaceFirst("SubClassOf", "SubClassOf:")
      editor.setText(rendering)
    true
  }

  def getInlineEditorComponent: JComponent = this.editingComponent

  @Nonnull override def getEditorTypeName = "OWL Axiom"

  override def canEdit(`object`: AnyRef): Boolean = classTag[Ax].runtimeClass.isInstance(`object`) //`object`.isInstanceOf[Ax]

  @Nonnull override def getEditorComponent: JComponent = this.editingComponent

  //  @Nullable override def getEditedObject: Ax = {
  //    try
  //      if (editor.isWellFormed) editor.createObject
  //      else null
  //    catch
  //      case _: OWLException => null
  //  }

  @throws[OWLExpressionParserException]
  override def getEditedObject: Ax = {
    editor.createObject
  }

  override def dispose(): Unit = {}

  override def addStatusChangedListener(listener: InputVerificationStatusChangedListener): Unit = {
    this.editor.addStatusChangedListener(listener)
  }

  override def removeStatusChangedListener(listener: InputVerificationStatusChangedListener): Unit = {
    this.editor.removeStatusChangedListener(listener)
  }

  def addDocumentListener(listener: DocumentListener): Unit = {
    this.editor.getDocument.addDocumentListener(listener)
  }

  def removeDocumentListener(listener: DocumentListener): Unit = {
    this.editor.getDocument.removeDocumentListener(listener)
  }

}
