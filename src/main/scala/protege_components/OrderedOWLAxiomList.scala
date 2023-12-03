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
import javax.swing.event.{DocumentEvent, ListDataEvent, ListDataListener}
import scala.reflect.ClassTag

class OrderedOWLAxiomList[Ax <: OWLAxiom : ClassTag](label: String,
                                                     rowLabel: String,
                                                     unexpectedAxiomException: () => OWLExpressionParserException = () => OWLExpressionParserException("Expected an OWL axiom", 0, 0, false, false, false, false, false, false, Collections.emptySet),
                                                     getOWLExceptionIfAxiomIsNotAllowed: Ax => Option[OWLException] = (_: Ax) => None,
                                                     orderedByInsertion: Boolean = true)
                                                    (using owlEditorKit: OWLEditorKit, p: ProtegeWorkerPool)
                                                    (implicit classTag_OrderedOWLAxiomListFrameSectionRow_Ax: ClassTag[OrderedOWLAxiomListFrameSectionRow[Ax]])
  extends OWLFrameList[java.util.Set[Ax]](owlEditorKit, OrderedOWLAxiomListFrame[Ax]()) {

  private val frame: OrderedOWLAxiomListFrame[Ax] = getFrame.asInstanceOf[OrderedOWLAxiomListFrame[Ax]]
  private val rowComparator: Comparator[OrderedOWLAxiomListFrameSectionRow[Ax]] =
    if orderedByInsertion then
      (o1: OrderedOWLAxiomListFrameSectionRow[Ax], o2: OrderedOWLAxiomListFrameSectionRow[Ax]) => (axioms indexOf o1.getAxiom) - (axioms indexOf o2.getAxiom)
    else
      val owlObjectComparator = owlEditorKit.getOWLModelManager.getOWLObjectComparator
      (o1: OrderedOWLAxiomListFrameSectionRow[Ax], o2: OrderedOWLAxiomListFrameSectionRow[Ax]) => owlObjectComparator.compare(o1.getAxiom, o2.getAxiom)
  frame.addSection(OrderedOWLAxiomListFrameSection(label, rowLabel, frame, rowComparator))

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
      // case row: OrderedOWLAxiomListFrameSectionRow[Ax] =>
      // case classTag[OrderedOWLAxiomListFrameSectionRow[Ax]](row) =>
      case classTag_OrderedOWLAxiomListFrameSectionRow_Ax(row) =>
        val editButton = MListEditButton((_: ActionEvent) => {
          SwingUtilities.invokeLater(() => {
            inputAxiom(row.getAxiom).foreach(replace(row.getAxiom, _))
          })
        })
        val deleteButton = MListDeleteButton((_: ActionEvent) => {
          SwingUtilities.invokeLater(() => {
            remove(row.getAxiom)
          })
        })
        util.List.of(deleteButton, editButton)
      case _ => Collections.emptyList[MListButton]
  }

  private var maybeWorker: Option[ProtegeWorker[_, Void]] = None
  private def asynchronouslyInTheWorker[T](message: String)(code: => T): ProtegeWorker[T, Void] = {
    maybeWorker.synchronized {
      maybeWorker.foreach(_.cancel(false))
      val worker = p.asynchronouslyInNewWorker(message) { code }
      maybeWorker = Some(worker)
      worker
    }
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
    val documentListener: SimpleDocumentListener = (_: DocumentEvent) => {
      unwantedConsequenceStatusLabel.setText("Please wait...")
      try {
        val axiom = unwantedConsequenceAxiomEditor.getEditedObject()
        asynchronouslyInTheWorker("Checking whether the input is a well-formed query.") {
          Thread.sleep(100)
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
    unwantedConsequenceAxiomEditorComponent.setEnabled(true)
    val pane = JOptionPane(panel, JOptionPane.PLAIN_MESSAGE, JOptionPane.OK_CANCEL_OPTION, null, Array[Object](okButton, cancelButton), null)
    okButton.addActionListener(_ => { pane.setValue(JOptionPane.OK_OPTION) })
    cancelButton.addActionListener(_ => { pane.setValue(JOptionPane.CANCEL_OPTION) })
    val dialog = pane.createDialog("Axiom Editor")
    dialog.setResizable(true)
    dialog.setMinimumSize(Dimension(320, 480))
    dialog.setVisible(true)
    unwantedConsequenceAxiomEditor.removeDocumentListener(documentListener)
    // unwantedConsequenceAxiomEditor.dispose()
    pane.getValue match
      case JOptionPane.CANCEL_OPTION => None
      case JOptionPane.OK_OPTION => Some(unwantedConsequenceAxiomEditor.getEditedObject())
  }

  private val axioms = Lists.newCopyOnWriteArrayList[Ax] // Sets.newConcurrentHashSet[Ax]

  setRootObject(Collections.emptySet[Ax])

  def refresh(): Unit = {
    setRootObject(java.util.HashSet[Ax](axioms))
    refreshComponent()
    validate()
    repaint()
  }

  def add(axiom: Ax): Unit = {
    if (!axioms.contains(axiom))
      axioms.add(axiom)
      val index = axioms.indexOf(axiom)
      listDataListeners.foreach(_.intervalAdded(ListDataEvent(this, ListDataEvent.INTERVAL_ADDED, index, index)))
    refresh()
  }

  def replace(oldAxiom: Ax, newAxiom: Ax): Unit = {
    val index = axioms.indexOf(oldAxiom)
    axioms.set(index, newAxiom)
    listDataListeners.foreach(_.contentsChanged(ListDataEvent(this, ListDataEvent.CONTENTS_CHANGED, index, index)))
    refresh()
  }

  def remove(axiom: Ax): Unit = {
    val index = axioms.indexOf(axiom)
    axioms.remove(axiom)
    listDataListeners.foreach(_.intervalRemoved(ListDataEvent(this, ListDataEvent.INTERVAL_REMOVED, index, index)))
    refresh()
  }

  def clear(): Unit = {
    val length = axioms.size()
    axioms.clear()
    listDataListeners.foreach(_.intervalRemoved(ListDataEvent(this, ListDataEvent.INTERVAL_REMOVED, 0, length - 1)))
    refresh()
  }

  def set(content: java.util.Collection[Ax]): Unit = {
    axioms.clear()
    axioms.addAll(content)
    val length = axioms.size()
    listDataListeners.foreach(_.contentsChanged(ListDataEvent(this, ListDataEvent.CONTENTS_CHANGED, 0, length - 1)))
    refresh()
  }

  def isEmpty: Boolean = {
    axioms.isEmpty
  }

  def length(): Int = {
    axioms.size()
  }

  def forEach(consumer: Ax => Unit): Unit = {
    axioms.forEach(consumer(_))
  }

  def stream(): java.util.stream.Stream[Ax] = {
    axioms.stream()
  }

  override def dispose(): Unit = {
    maybeWorker.foreach(_.cancel(true))
    listDataListeners.clear()
    axioms.clear()
    super.dispose()
  }

  private val listDataListeners = collection.mutable.HashSet[ListDataListener]()

  def addListDataListener(l: ListDataListener): Unit = {
    if l != null then listDataListeners += l
  }

  def addListDataListener(processEvent: ListDataEvent => Unit): ListDataListener = {
    val l = new ListDataListener() {
      def contentsChanged(e: ListDataEvent): Unit = processEvent(e)
      def intervalAdded(e: ListDataEvent): Unit = processEvent(e)
      def intervalRemoved(e: ListDataEvent): Unit = processEvent(e)
    }
    addListDataListener(l)
    l
  }

  def removeListDataListener(l: ListDataListener): Unit = {
    if l != null then listDataListeners -= l
  }

}
