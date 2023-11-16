package de.tu_dresden.inf.lat
package protege_components

import protege_components.Util.*

import com.google.common.collect.Lists
import org.protege.editor.core.ui.list.*
import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.model.classexpression.OWLExpressionParserException
import org.protege.editor.owl.ui.framelist.OWLFrameList
import org.semanticweb.owlapi.model.{OWLAxiom, OWLException}

import java.awt.*
import java.awt.event.ActionEvent
import java.util
import java.util.{Collections, Comparator, List, Set}
import javax.swing.*
import javax.swing.event.DocumentEvent
import scala.reflect.ClassTag

import protege_components.ProtegeWorker.*

class OrderedOWLAxiomList[Ax <: OWLAxiom : ClassTag](label: String,
                                                     rowLabel: String,
                                                     unexpectedAxiomException: () => OWLExpressionParserException = () => OWLExpressionParserException("Expected an OWL axiom", 0, 0, false, false, false, false, false, false, Collections.emptySet),
                                                     getOWLExceptionIfAxiomIsNotAllowed: Ax => Option[OWLException] = (_: Ax) => None)
                                                    (using owlEditorKit: OWLEditorKit)
                                                    (implicit classTag_OrderedOWLAxiomListFrameSectionRow_Ax: ClassTag[OrderedOWLAxiomListFrameSectionRow[Ax]])
  extends OWLFrameList[java.util.Set[Ax]](owlEditorKit, OrderedOWLAxiomListFrame[Ax]()) {

  private val frame: OrderedOWLAxiomListFrame[Ax] = getFrame.asInstanceOf[OrderedOWLAxiomListFrame[Ax]]
  private val rowComparator: Comparator[OrderedOWLAxiomListFrameSectionRow[Ax]] =
    (o1: OrderedOWLAxiomListFrameSectionRow[Ax], o2: OrderedOWLAxiomListFrameSectionRow[Ax]) => {
      (axioms indexOf o1.getAxiom) - (axioms indexOf o2.getAxiom)
    }
  frame.addSection(OrderedOWLAxiomListFrameSection(label, rowLabel, frame, rowComparator));

  override def handleDelete(): Unit = super.handleDelete() // revert to public access to avoid compiling error

  var isEditable = true

  private val addButton = MListAddButton((_: ActionEvent) => {
    SwingUtilities.invokeLater(() => {
      inputAxiom().foreach(add)
    })
  })

  override protected def getButtons(value: Object): java.util.List[MListButton] = {
    if isEditable then
      value match
        case _: MListSectionHeader => Collections.singletonList(addButton)
        case item: MListItem => getListItemButtons(item)
    else Collections.emptyList()
  }

  override protected def getListItemButtons(item: MListItem): util.List[MListButton] = {
    item match
//      case row: OrderedOWLAxiomListFrameSectionRow[Ax] =>
//      case classTag[OrderedOWLAxiomListFrameSectionRow[Ax]](row) =>
      case classTag_OrderedOWLAxiomListFrameSectionRow_Ax(row) =>
        val editButton = MListEditButton((_: ActionEvent) => {
          SwingUtilities.invokeLater(() => {
            inputAxiom(row.getAxiom()).foreach(replace(row.getAxiom(), _))
          })
        })
        val deleteButton = MListDeleteButton((_: ActionEvent) => {
          SwingUtilities.invokeLater(() => {
            remove(row.getAxiom())
          })
        })
        util.List.of(deleteButton, editButton)
      case _ => Collections.emptyList[MListButton]
  }

//  private var worker: Option[ProtegeWorker[Option[OWLException], Void]] = None
//  private def asynchronouslyInTheWorker(code: => Option[OWLException]): ProtegeWorker[Option[OWLException], Void] = {
//    worker.foreach(_.cancel(true))
//    val w: ProtegeWorker[Option[OWLException], Void] = () => { code }
//    worker = Some(w)
//    w.message = "Checking whether the input is a well-formed query."
//    w
//  }
  private var maybeWorker: Option[ProtegeWorker[_, Void]] = None
  private def asynchronouslyInTheWorker[T](message: String)(code: => T): ProtegeWorker[T, Void] = {
    maybeWorker.foreach(_.cancel(true))
    val worker = asynchronouslyInNewWorker(message) { code }
    maybeWorker = Some(worker)
    worker
  }

  private def inputAxiom(initialValue: Ax | Null = null): Option[Ax] = {
    val unwantedConsequenceAxiomEditor = OWLAxiomEditor[Ax](owlEditorKit, unexpectedAxiomException)
    val unwantedConsequenceAxiomEditorComponent = unwantedConsequenceAxiomEditor.getEditorComponent().getComponent(0)
    val (unwantedConsequenceStatusPanel, unwantedConsequenceStatusLabel) = breakingJLabelInJPanel(" ")
    val panel = JPanel()
    panel.setLayout(GridBagLayout())
    panel.add(
      JScrollPane(
        unwantedConsequenceAxiomEditorComponent,
        ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED),
      GridBagConstraints(
        1, 4, // gridx, gridy
        1, 1, // gridwidth, gridheight
        1, 1, // weightx, weighty
        GridBagConstraints.CENTER, // anchor
        GridBagConstraints.BOTH, // fill
        Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    panel.add(
      unwantedConsequenceStatusPanel,
      GridBagConstraints(
        1, 5, // gridx, gridy
        1, 1, // gridwidth, gridheight
        0, 0, // weightx, weighty
        GridBagConstraints.LINE_START, // anchor
        GridBagConstraints.HORIZONTAL, // fill
        Insets(0, 0, 0, 0), // insets
        4, 4 // ipadx, ipady
      ))
    val okButton = JButton("OK")
    val cancelButton = JButton("Cancel")
//    val statusChangedListener: InputVerificationStatusChangedListener = _ => {
//      unwantedConsequenceStatusLabel.setText("Please wait...")
//      try {
//        val axiom = unwantedConsequenceAxiomEditor.getEditedObject()
//        checkIfAxiomIsAllowed(axiom)
//        okButton.setEnabled(true)
//        unwantedConsequenceStatusLabel.setText("The axiom can be added to the repair request.")
//      } catch {
//        case e: OWLException =>
//          okButton.setEnabled(false)
//          unwantedConsequenceStatusLabel.setText(asHTMLMessage(e.getMessage))
//      }
//    }
//    unwantedConsequenceAxiomEditor.addStatusChangedListener(statusChangedListener)
    val documentListener: SimpleDocumentListener = (_: DocumentEvent) => {
      unwantedConsequenceStatusLabel.setText("Please wait...")
      try {
        val axiom = unwantedConsequenceAxiomEditor.getEditedObject()
        asynchronouslyInTheWorker("Checking whether the input is a well-formed query.") {
          getOWLExceptionIfAxiomIsNotAllowed(axiom)
        } executeAndThen {
          maybeOWLException =>
            if maybeOWLException.isEmpty then
              okButton.setEnabled(true)
              unwantedConsequenceStatusLabel.setText("The axiom can be added to the repair request.")
            else
              okButton.setEnabled(false)
              unwantedConsequenceStatusLabel.setText(asHTMLMessage(maybeOWLException.get.getMessage))
        }
      } catch {
        case e: OWLException =>
          okButton.setEnabled(false)
          unwantedConsequenceStatusLabel.setText(asHTMLMessage(e.getMessage))
      }
    }
    unwantedConsequenceAxiomEditor.addDocumentListener(documentListener)
    if initialValue != null then unwantedConsequenceAxiomEditor.setEditedObject(initialValue.asInstanceOf[Ax])
//    statusChangedListener.verifiedStatusChanged(true)
    unwantedConsequenceAxiomEditorComponent.setEnabled(true)
    val pane = JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
    okButton.addActionListener(_ => { pane.setValue(JOptionPane.OK_OPTION) })
    cancelButton.addActionListener(_ => { pane.setValue(JOptionPane.CANCEL_OPTION) })
    val dialog = pane.createDialog("Axiom Editor")
    dialog.setResizable(true)
    dialog.setMinimumSize(Dimension(320, 480))
    dialog.setVisible(true)
//    val axiom = unwantedConsequenceAxiomEditor.getEditedObject()
//    unwantedConsequenceAxiomEditor.removeStatusChangedListener(statusChangedListener)
    unwantedConsequenceAxiomEditor.removeDocumentListener(documentListener)
//    unwantedConsequenceAxiomEditor.dispose()
    pane.getValue match
      case JOptionPane.CANCEL_OPTION => None
      case JOptionPane.OK_OPTION => Some(unwantedConsequenceAxiomEditor.getEditedObject())
  }

  private val axioms = Lists.newCopyOnWriteArrayList[Ax] // Sets.newConcurrentHashSet[Ax]

  setRootObject(Collections.emptySet[Ax])

  def refresh() = {
    setRootObject(java.util.HashSet[Ax](axioms))
    refreshComponent()
    validate()
    repaint()
  }

  def add(axiom: Ax) = {
    if (!axioms.contains(axiom))
      axioms.add(axiom)
    refresh()
  }

  def replace(oldAxiom: Ax, newAxiom: Ax) = {
    axioms.set(axioms.indexOf(oldAxiom), newAxiom)
    refresh()
  }

  def remove(axiom: Ax) = {
    axioms.remove(axiom)
    refresh()
  }

  def clear() = {
    axioms.clear()
    refresh()
  }

  def set(content: java.util.Collection[Ax]) = {
    axioms.clear()
    axioms.addAll(content)
    refresh()
  }

  def forEach(consumer: Ax => Unit) = {
    axioms.forEach(consumer(_))
  }

  def stream(): java.util.stream.Stream[Ax] = {
    axioms.stream()
  }

  override def dispose() = {
    axioms.clear()
    maybeWorker.foreach(_.cancel(true))
    super.dispose()
  }

}
