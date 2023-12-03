package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Answer.*
import protege_components.Util.*
import protege_components.{OrderedOWLAxiomList, OrderedOWLAxiomListFrameSectionRow, ProtegeWorkerPool, TextMListButton}

import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.model.classexpression.OWLExpressionParserException
import org.protege.editor.owl.model.event.EventType
import org.protege.editor.owl.ui.view.AbstractOWLViewComponent
import org.semanticweb.owlapi.apibinding.OWLManager
import org.semanticweb.owlapi.model.*
import org.semanticweb.owlapi.model.parameters.Imports

import java.awt.*
//import java.awt.event.{WindowEvent, WindowListener}
import java.util.Collections
import javax.swing.*
import scala.jdk.CollectionConverters.*
import scala.jdk.StreamConverters.*
import scala.reflect.ClassTag

object InteractiveOptimalRepairViewComponent {
  private val instances = java.util.concurrent.ConcurrentHashMap[OWLOntologyID, InteractiveOptimalRepairViewComponent]().asScala
}

class InteractiveOptimalRepairViewComponent extends AbstractOWLViewComponent {

  private lazy val p = ProtegeWorkerPool()

  private val classTag_OrderedOWLAxiomListFrameSectionRow_Query = implicitly[ClassTag[OrderedOWLAxiomListFrameSectionRow[Query]]]

  private var maybeActiveOntologyID: Option[OWLOntologyID] = None

  protected def initialiseOWLView(): Unit = {
    getOWLModelManager.addListener(event => {
      if event.getType equals EventType.ACTIVE_ONTOLOGY_CHANGED then
        updateForActiveOntology()
    })
    updateForActiveOntology()
  }

  private def updateForActiveOntology(): Unit = {
    val activeOntologyID = getOWLModelManager.getActiveOntology.getOntologyID
    if InteractiveOptimalRepairViewComponent.instances.get(activeOntologyID).forall(_ equals this) then
      maybeActiveOntologyID = Some(activeOntologyID)
      InteractiveOptimalRepairViewComponent.instances(activeOntologyID) = this
      disposeOfRepairInProgress()
      showInitialView()
    else
      maybeActiveOntologyID = None
      this.removeAll()
      this.setLayout(BorderLayout())
      this.add(JLabel("The interactive-optimal-repair view component is already shown elsewhere for the selected ontology.  Please continue there."), BorderLayout.NORTH)
      this.revalidate()
      this.repaint()
  }

  private val onDisposalCode = collection.mutable.Queue[() => Unit]()

  private def onDisposal(code: => Unit): Unit = {
    onDisposalCode.enqueue(() => code)
  }

  private def disposeOfRepairInProgress(): Unit = {
    while onDisposalCode.nonEmpty do
      onDisposalCode.dequeue()()
    p.cancelActiveWorkers()
  }

  private def showInitialView(): Unit = {
    this.removeAll()
    this.setLayout(GridBagLayout())
    val readMe =
      "<html>" +
        "<h1>Interactive Optimal Repair</h1>" +
        "<p>TBA</p>" +
        "</html>"
    add(breakingJLabel(readMe),
      GridBagConstraints()
        .coordinates(0, 0)
        .anchor(GridBagConstraints.FIRST_LINE_START)
        .weight(1, 0)
        .fill(GridBagConstraints.HORIZONTAL)
        .insets(32, 32, 32, 32))

    val startButton = JButton("Start")
    startButton.setPreferredSize(Dimension(256, 48))
    startButton.addActionListener(_ => startUserInteraction())
    this.add(startButton,
      GridBagConstraints()
        .coordinates(0, 1)
        .insets(32, 0, 0, 0))

    this.add(JLabel(),
      GridBagConstraints()
        .coordinates(0, 2)
        .weight(1, 1)
        .fill(GridBagConstraints.BOTH))

    this.revalidate()
    this.repaint()
  }

  private def startUserInteraction(): Unit = {

    given ontologyManager: OWLOntologyManager = OWLManager.createOWLOntologyManager() // getOWLModelManager.getOWLOntologyManager
    val activeOntology = getOWLModelManager.getActiveOntology

    // The following workaround is necessary since a method `setMutable(mutable: Boolean)` is not available in class `org.protege.editor.owl.model.OWLModelManager`.
    val impendingOWLOntologyChangeListener: ImpendingOWLOntologyChangeListener = changes => {
      for (change <- changes.asScala)
        if change.getOntology equals activeOntology then
          JOptionPane.showMessageDialog(this, "The active ontology must not be changed during repair.  The change has been dismissed.", "Warning", JOptionPane.WARNING_MESSAGE)
          throw OWLOntologyChangeVetoException(change.getChangeData, "The active ontology must not be changed during repair.  The change has been dismissed.")
    }
    getOWLModelManager.getOWLOntologyManager.addImpendingOntologyChangeListener(impendingOWLOntologyChangeListener)

    val panel = JPanel(BorderLayout(16, 16))
    this.removeAll()
    this.setLayout(BorderLayout(16, 16))
    this.add(panel, BorderLayout.CENTER)
    panel.add(breakingJLabel("Please wait while it is determined if the active ontology is supported..."), BorderLayout.NORTH)
//    val pane = JOptionPane(panel)
//    val dialog = pane.createDialog(InteractiveOptimalRepairViewComponent.this, "Interactive Optimal Repair")
//    // dialog.setAlwaysOnTop(true)
//    dialog.setModalityType(Dialog.ModalityType.MODELESS)
//    dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE)
//    dialog.addWindowListener(new WindowListener() {
//      def windowOpened(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      def windowClosing(event: java.awt.event.WindowEvent): Unit = { dialog.dispose() }
//      def windowClosed(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      def windowActivated(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      def windowDeactivated(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      def windowIconified(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      def windowDeiconified(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//    })
//    def whenDialogClosed(code: => Unit): Unit = {
//      dialog.addWindowListener(new WindowListener() {
//        def windowOpened(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//        def windowClosing(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//        def windowClosed(event: java.awt.event.WindowEvent): Unit = { code }
//        def windowActivated(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//        def windowDeactivated(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//        def windowIconified(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//        def windowDeiconified(event: java.awt.event.WindowEvent): Unit = { /* Do nothing. */ }
//      })
//    }
//    whenDialogClosed {
//      panel.removeAll()
//      p.cancelActiveWorkers()
//      getOWLModelManager.getOWLOntologyManager.removeImpendingOntologyChangeListener(impendingOWLOntologyChangeListener)
//    }
//    dialog.setResizable(true)
//    dialog.setMinimumSize(Dimension(640, 480))
//

    onDisposal {
      p.cancelActiveWorkers()
      getOWLModelManager.getOWLOntologyManager.removeImpendingOntologyChangeListener(impendingOWLOntologyChangeListener)
    }

    val cancelButton = JButton("Cancel")
    cancelButton.setFixedSize(Dimension(256, 32))
    cancelButton.addActionListener(_ => {
//      dialog.dispose()
      disposeOfRepairInProgress()
      showInitialView()
    })
    val nextButton = JButton("Next")
    nextButton.setFixedSize(Dimension(256, 32))
    nextButton.setEnabled(false)
//    pane.setOptions(Array(cancelButton, nextButton))
//    dialog.setVisible(true)
    this.add(
      Box.createHorizontalBox()
        ._add(Box.createHorizontalGlue())
        ._add(cancelButton)
        ._add(Box.createRigidArea(Dimension(16, 32)))
        ._add(nextButton)
        ._add(Box.createHorizontalGlue()),
      BorderLayout.SOUTH
    )
    this.revalidate()
    this.repaint()
    p.asynchronouslyInNewWorker("Checking whether the active ontology is supported...") {
      ELExpressivityChecker.check(activeOntology)
    } executeAndThen {
      isSupported => {
        panel.removeAll()
        panel.add(breakingJLabel(if isSupported then "The active ontology is supported." else "The active ontology is currently not supported since it contains axioms not expressible in 𝓔𝓛.  A future version will widen support towards Horn-𝓐𝓛𝓒𝓡𝓞𝓘."), BorderLayout.NORTH)
        panel.revalidate()
        panel.repaint()

        if isSupported then {

//          p.asynchronouslyInNewWorker("Initializing the terminology reasoner...") {
//            val terminology = ontologyManager.createOntology(activeOntology.getTBoxAxioms(Imports.INCLUDED))
//            val terminologyReasoner = ElkReasonerFactory().createReasoner(terminology)
//            whenDialogClosed {
//              terminologyReasoner.dispose()
//              ontologyManager.removeOntology(terminology)
//            }
//            terminologyReasoner.flush()
//            terminologyReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
//            (terminology, terminologyReasoner)
//          } inParallelWith p.asynchronouslyInNewWorker("Initializing the ontology reasoner...") {
//            val ontologyReasoner = ElkReasonerFactory().createReasoner(activeOntology)
//            whenDialogClosed {
//              ontologyReasoner.dispose()
//            }
//            ontologyReasoner.flush()
//            ontologyReasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS)
//            ontologyReasoner
//          } executeAndThen {
//            case ((terminology, terminologyReasoner), ontologyReasoner) => {
          p.asynchronouslyInNewWorker("Initializing the reasoner...") {
            val reasoner = ExtendedClassificationForMultipleABoxesWithSharedTBox(activeOntology, Set.empty, true)
            val emptyABoxIndex = reasoner.registerABox(Set.empty)
            (reasoner, emptyABoxIndex)
          } executeAndThen {
            (reasoner, emptyABoxIndex) => {
              nextButton.enableWithSingleActionListener(_ => {
                /* State 0: Repair Request */
                nextButton.setEnabled(false)
                panel.removeAll()
                panel.add(breakingJLabel("Please specify the unwanted consequences for which the active ontology is to be repaired.  Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported.  Support will be extended towards Horn-𝓐𝓛𝓒𝓡𝓞𝓘 as well as concept inclusions (C SubClassOf: D) in a future version."), BorderLayout.NORTH)

                val positiveRepairRequestABoxIndex = reasoner.registerABox(Set.empty)

                given pool: ProtegeWorkerPool = p
                given owlEditorKit: OWLEditorKit = getOWLEditorKit
                val negativeRepairRequestAxiomList: OrderedOWLAxiomList[Query] =
                  OrderedOWLAxiomList[Query]("Repair Request (negative axioms to be not entailed)", "Unwanted Consequence",
                    () => OWLExpressionParserException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported.", 0, 0, false, false, false, false, false, false, Collections.emptySet),
                    axiom => {
                      if !ELExpressivityChecker.checkAxiom(axiom) then Some(OWLException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported."))
//                      else if terminologyReasoner.isEntailed(axiom) then Some(OWLException("Tautologies cannot be removed."))
//                      else if !ontologyReasoner.isEntailed(axiom) then Some(OWLException("The axiom is not entailed by the active ontology and thus need not be repaired for."))
                      else if reasoner.entails(emptyABoxIndex, axiom) then Some(OWLException("Tautologies cannot be removed."))
                      else if !reasoner.entails(axiom) then Some(OWLException("The axiom is not entailed by the active ontology and thus need not be repaired for."))
                      else if reasoner.entails(positiveRepairRequestABoxIndex, axiom) then Some(OWLException("The axiom is already entailed by the below specified positive axioms."))
                      else None
                    })
                negativeRepairRequestAxiomList.addListDataListener(_ => { nextButton.setEnabled(!negativeRepairRequestAxiomList.isEmpty) })
//                panel.add(JScrollPane(negativeRepairRequestAxiomList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER), BorderLayout.CENTER)

                val positiveRepairRequestAxiomList: OrderedOWLAxiomList[Query] =
                  OrderedOWLAxiomList[Query]("Repair Request (positive axioms to be entailed)", "Wanted Consequence",
                    () => OWLExpressionParserException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported.", 0, 0, false, false, false, false, false, false, Collections.emptySet),
                    axiom => {
                      if !ELExpressivityChecker.checkAxiom(axiom) then Some(OWLException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported."))
                      // TODO: Automatically add non-entailed axioms.
                      else if !reasoner.entails(axiom) then Some(OWLException("The axiom is not entailed by the active ontology and thus needs to be added first."))
                      else if {
                        reasoner.addAxiomAndFlush(positiveRepairRequestABoxIndex, axiom)
                        val error = negativeRepairRequestAxiomList.stream().toScala(LazyList).toSet exists { x => reasoner.entails(positiveRepairRequestABoxIndex, x) }
                        reasoner.removeAxiomAndFlush(positiveRepairRequestABoxIndex, axiom)
                        error
                      } then Some(OWLException("This axiom together with the already specified positive axioms entails some negative axiom."))
                      else None
                    })
                positiveRepairRequestAxiomList.addListDataListener(_ => {
                  reasoner.replaceABox(positiveRepairRequestABoxIndex, positiveRepairRequestAxiomList.stream().toScala(LazyList).toSet)
                })
                panel.add(
                  Box.createVerticalBox()
                    ._add(JScrollPane(negativeRepairRequestAxiomList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER))
                    ._add(Box.createVerticalStrut(16))
                    ._add(JScrollPane(positiveRepairRequestAxiomList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER)),
                  BorderLayout.CENTER)

                panel.revalidate()
                panel.repaint()
                nextButton.setSingleActionListener(_ => {
                  /* State 1: Interaction Strategy */
                  nextButton.setEnabled(false)
                  panel.removeAll()
//                  terminologyReasoner.dispose()
//                  ontologyManager.removeOntology(terminology)
//                  ontologyReasoner.dispose()
                  reasoner.unregisterABox(emptyABoxIndex)
                  val strategyRadioButtons = Strategy.values.map(s => (JRadioButton(htmlParagraph("<b>" + s.name + "</b> (" + s.description + ")")), s)).toMap
                  val strategyRadioButtonGroup = ButtonGroup()
                  strategyRadioButtons.keys.foreach(strategyRadioButtonGroup.add)
                  val strategyRadioButtonPanel = JPanel()
                  strategyRadioButtonPanel.setLayout(BoxLayout(strategyRadioButtonPanel, BoxLayout.Y_AXIS))
                  strategyRadioButtons.keys.foreach(strategyRadioButtonPanel.add)
                  strategyRadioButtons.keys.foreach(b => b.addActionListener(_ => { if b.isSelected then nextButton.setEnabled(true) })) // should be moved below setting the action listener for very fast users

                  val wantedConsequences = positiveRepairRequestAxiomList.stream().toScala(LazyList).toSet
                  if wantedConsequences.nonEmpty then
                    strategyRadioButtons.foreach {
                      case (button, strategy) =>
                        strategy match
                          case Strategy.SMARTv2 => // Supported strategy
                          case _ => button.setEnabled(false)
                    }

                  panel.add(breakingJLabel("Please select an interaction strategy."), BorderLayout.NORTH)
                  panel.add(strategyRadioButtonPanel, BorderLayout.CENTER)
                  panel.revalidate()
                  panel.repaint()
                  nextButton.setSingleActionListener(_ => {
                    /* State 2: User Interaction */
                    nextButton.setEnabled(false)

                    panel.removeAll()
                    val unwantedConsequences = negativeRepairRequestAxiomList.stream().toScala(LazyList).toSet
                    val wantedConsequences = positiveRepairRequestAxiomList.stream().toScala(LazyList).toSet
                    val repairRequest = RepairRequest(unwantedConsequences, wantedConsequences)
                    val strategy = strategyRadioButtons.keys.find(_.isSelected).map(strategyRadioButtons).get

                    p.asynchronouslyInNewWorker("Generating the repair configuration and updating the reasoner...") {
                      RepairConfiguration(activeOntology, repairRequest, reasoner)
                    } executeAndThen { _repairConfiguration =>

                      given repairConfiguration: RepairConfiguration = _repairConfiguration
//                      whenDialogClosed { repairConfiguration.dispose() }
                      onDisposal {
                        repairConfiguration.dispose()
                      }
                      val userInteraction = UserInteraction(strategy)

                      def lock(list: OrderedOWLAxiomList[Query]): Unit = {
                        list.isEditable = false
                        list.refresh()
                      }

                      def unlock(list: OrderedOWLAxiomList[Query]): Unit = {
                        list.isEditable = true
                        list.refresh()
                      }

                      def newAcceptButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Accept",
                          Color.GREEN.darker(),
                          "\u2713",
                          14,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer ACCEPT to query " + query + "...") {
                              userInteraction.receiveAnswer(query, ACCEPT)
                            } executeAndThen { _ => unlock(list) }
                          })

                      def newIgnoreButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Ignore",
                          Color.GRAY.darker(),
                          "?",
                          14,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer IGNORE to query " + query + "...") {
                              userInteraction.receiveAnswer(query, IGNORE)
                            } executeAndThen { _ => unlock(list) }
                          })

                      def newDeclineButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Decline",
                          Color.RED.darker(),
                          "\u2715",
                          15,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer DECLINE to query " + query + "...") {
                              userInteraction.receiveAnswer(query, DECLINE)
                            } executeAndThen { _ => unlock(list) }
                          })

                      def newInheritedAcceptButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Confirm inherited accept answer",
                          Color.GREEN.darker(),
                          "\u2713",
                          14,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer INHERITED_ACCEPT to query " + query + "...") {
                              userInteraction.receiveAnswer(query, INHERITED_ACCEPT)
                            } executeAndThen { _ => unlock(list) }
                          })

                      def newInheritedDeclineButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Confirm inherited decline answer",
                          Color.RED.darker(),
                          "\u2715",
                          15,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer INHERITED_DECLINE to query " + query + "...") {
                              userInteraction.receiveAnswer(query, INHERITED_DECLINE)
                            } executeAndThen { _ => unlock(list) }
                          })

                      def newRollbackButton(list: OrderedOWLAxiomList[Query], query: Query) =
                        TextMListButton(
                          "Rollback",
                          Color.BLUE.darker(),
                          "\u293a", // "\u238c"
                          28,
                          _ => {
                            lock(list)
                            p.asynchronouslyInNewWorker("Processing user answer ROLLBACK to query " + query + "...") {
                              userInteraction.receiveAnswer(query, ROLLBACK)
                            } executeAndThen { _ => unlock(list) }
                          })

                      val repairSeedInteractionAxiomList: OrderedOWLAxiomList[Query] =
                        new OrderedOWLAxiomList[Query]("Questions", "Question") {
                          override protected def getButtons(value: Object): java.util.List[MListButton] = {
                            value match
                              case classTag_OrderedOWLAxiomListFrameSectionRow_Query(row) if isEditable =>
                                Answer.values.filter(userInteraction.getButtonTypes(row.getAxiom)).map({
                                  case ACCEPT => newAcceptButton(this, row.getAxiom)
                                  case IGNORE => newIgnoreButton(this, row.getAxiom)
                                  case DECLINE => newDeclineButton(this, row.getAxiom)
                                  case INHERITED_ACCEPT => newInheritedAcceptButton(this, row.getAxiom)
                                  case INHERITED_DECLINE => newInheritedDeclineButton(this, row.getAxiom)
                                  case ROLLBACK => newRollbackButton(this, row.getAxiom)
                                }).toList.asJava
                              case _ => Collections.emptyList()
                          }
                        }
                      repairSeedInteractionAxiomList.isEditable = true

                      val userInterface = new UserInterface() {
                        override def showQuestion(query: Query): Unit =
                          invokeLaterOnProtegeThread {
                            repairSeedInteractionAxiomList.add(query)
                          }
                        override def removeQuestion(query: Query): Unit =
                          invokeLaterOnProtegeThread {
                            repairSeedInteractionAxiomList.remove(query)
                          }
                      }

                      panel.add(breakingJLabel("Please carefully assess each of the below axioms.  More specifically, please accept each valid axiom and decline each invalid axiom.  If you are unsure, you could also ignore some axioms, but then the repair might not be satisfactory.  After all questions have been considered, the induced optimal repair will be computed by clicking the below button."), BorderLayout.NORTH)
                      panel.add(JScrollPane(repairSeedInteractionAxiomList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER), BorderLayout.CENTER)
                      panel.revalidate()
                      panel.repaint()

                      p.asynchronouslyInNewWorker("User interaction is running...") {
                        userInteraction.start(userInterface)
                        while !userInteraction.hasBeenCompleted do Thread.sleep(1000)
                        userInteraction.dispose()
                        userInteraction.getRepairSeed
                      } inParallelWith p.asynchronouslyInNewWorker("Checking if the input ontology is acyclic...") {
//                        IQSaturation().isAcyclic
                        repairConfiguration.iqSaturation.isAcyclic
                      } executeAndThen {
                        (repairSeed, isAcyclic) => {
                          nextButton.enableWithSingleAction {
                            /* State 3 */
                            nextButton.setEnabled(false)
                            nextButton.setText("Compute")
                            panel.removeAll()

                            val queryLanguageRadioButtons = QueryLanguage.values.map(s => (JRadioButton(s.toString), s)).toMap
                            val queryLanguageRadioButtonGroup = ButtonGroup()
                            queryLanguageRadioButtons.keys.foreach(queryLanguageRadioButtonGroup.add)
                            val queryLanguageRadioButtonPanel = JPanel()
                            queryLanguageRadioButtonPanel.setLayout(BoxLayout(queryLanguageRadioButtonPanel, BoxLayout.Y_AXIS))
                            queryLanguageRadioButtons.keys.foreach(queryLanguageRadioButtonPanel.add)

                            val compatibilityModeRadioButtons = CompatibilityMode.values.map(s => (JRadioButton(htmlParagraph(s.description)), s)).toMap
                            val compatibilityModeRadioButtonGroup = ButtonGroup()
                            compatibilityModeRadioButtons.keys.foreach(compatibilityModeRadioButtonGroup.add)
                            val compatibilityModeRadioButtonPanel = JPanel()
                            compatibilityModeRadioButtonPanel.setLayout(BoxLayout(compatibilityModeRadioButtonPanel, BoxLayout.Y_AXIS))
                            compatibilityModeRadioButtons.keys.foreach(compatibilityModeRadioButtonPanel.add)

                            queryLanguageRadioButtons.keys.foreach(b => b.addActionListener(_ => {
                              if b.isSelected && compatibilityModeRadioButtons.keys.exists(_.isSelected) then nextButton.setEnabled(true)
                            })) // should be moved below setting the action listener for very fast users
                            compatibilityModeRadioButtons.keys.foreach(b => b.addActionListener(_ => {
                              if b.isSelected && queryLanguageRadioButtons.keys.exists(_.isSelected) then nextButton.setEnabled(true)
                            })) // should be moved below setting the action listener for very fast users

                            panel.setLayout(BoxLayout(panel, BoxLayout.Y_AXIS))
                            if isAcyclic then
                              panel.add(JLabel(htmlParagraph("The input ontology is acyclic and thus the repairs are equal for all query languages that contain all queries in the repair request.")))
                            panel.add(JLabel(htmlParagraph("With respect to which query language should the repair be computed?")))
                            panel.add(Box.createRigidArea(Dimension(0, 8)))
                            panel.add(queryLanguageRadioButtonPanel)
                            panel.add(Box.createRigidArea(Dimension(0,32)))
                            panel.add(JLabel(htmlParagraph("Should fresh named individuals be introduced instead of anonymous individuals?  Note that this has no impact on entailed queries, but can impair entailment with other (quantified) ABoxes.")))
                            panel.add(Box.createRigidArea(Dimension(0, 8)))
                            panel.add(compatibilityModeRadioButtonPanel)
                            panel.add(Box.createVerticalGlue())

                            // queryLanguageRadioButtons.foreach { case (button, QueryLanguage.IRQ) => button.setSelected(true); case (button, _) => button.setEnabled(false) }
                            queryLanguageRadioButtons.foreach { case (button, QueryLanguage.CQ) => button.setEnabled(false); case _ => }

                            panel.revalidate()
                            panel.repaint()

                            nextButton.setSingleActionListener(_ => {
                              /* State 4: Repair Computation */
                              nextButton.setEnabled(false)
                              nextButton.setText("Finish")
                              panel.removeAll()
                              panel.add(breakingJLabel("Please wait while the optimal repair is computed... Afterwards, the active ontology is replaced by the repaired ontology when the Finish button is clicked."), BorderLayout.NORTH)
                              panel.revalidate()
                              panel.repaint()
                              val queryLanguage = queryLanguageRadioButtons.keys.find(_.isSelected).map(queryLanguageRadioButtons).get
                              val compatibilityMode = compatibilityModeRadioButtons.keys.find(_.isSelected).map(compatibilityModeRadioButtons).get
                              p.asynchronouslyInNewWorker("Computing the repair...") {
                                Repair(queryLanguage, repairSeed).compute(compatibilityMode)
                              } executeAndThen {
                                repair => {
                                  nextButton.enableWithSingleActionListener(_ => {
                                    /* State 5: All Tasks Finished */
                                    getOWLModelManager.getOWLOntologyManager.removeImpendingOntologyChangeListener(impendingOWLOntologyChangeListener)
                                    p.asynchronouslyInNewWorker("Overwriting the active ontology with the repaired ontology...") {
                                      getOWLModelManager.getOWLOntologyManager.removeAxioms(activeOntology, activeOntology.getABoxAxioms(Imports.INCLUDED))
                                      getOWLModelManager.getOWLOntologyManager.addAxioms(activeOntology, repair.getABoxAxioms(Imports.INCLUDED))
                                    } executeAndThen {
//                                      dialog.dispose()
                                      disposeOfRepairInProgress()
                                      showInitialView()
                                    }
                                  })
                                }
                              }
                            })
                          }
                        }
                      }
                    }
                  })
                })
              })
            }
          }
        }
      }
    }
  }

  protected def disposeOWLView(): Unit = {
    maybeActiveOntologyID.foreach { InteractiveOptimalRepairViewComponent.instances.remove }
    disposeOfRepairInProgress()
  }

}
