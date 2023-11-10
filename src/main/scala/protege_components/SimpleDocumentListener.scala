package de.tu_dresden.inf.lat
package protege_components

import javax.swing.event.{DocumentEvent, DocumentListener}

abstract class SimpleDocumentListener() extends DocumentListener {

  def documentChanged(evt: DocumentEvent): Unit

  def insertUpdate(evt: DocumentEvent): Unit = documentChanged(evt)
  def removeUpdate(evt: DocumentEvent): Unit = documentChanged(evt)
  def changedUpdate(evt: DocumentEvent): Unit = documentChanged(evt)

}
