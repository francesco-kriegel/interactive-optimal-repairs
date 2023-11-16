package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import interactive_optimal_repairs.Answer.*
import protege_components.Util.*
import protege_components.{OrderedOWLAxiomList, OrderedOWLAxiomListFrameSectionRow, TextMListButton}

import org.protege.editor.core.ui.list.MListButton
import org.protege.editor.owl.OWLEditorKit
import org.protege.editor.owl.model.classexpression.OWLExpressionParserException
import org.protege.editor.owl.ui.view.AbstractOWLViewComponent
import org.semanticweb.elk.owlapi.ElkReasonerFactory
import org.semanticweb.owlapi.model.parameters.Imports
import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLException, OWLObjectPropertyAssertionAxiom, OWLOntologyManager}

import java.awt.*
import java.beans.{PropertyChangeEvent, PropertyChangeListener}
import java.util.Collections
import javax.swing.*
import scala.jdk.StreamConverters.*
import scala.reflect.ClassTag

import protege_components.ProtegeWorker.*

class InteractiveOptimalRepairViewComponent extends AbstractOWLViewComponent {

  private val classTag_OrderedOWLAxiomListFrameSectionRow_Query = implicitly[ClassTag[OrderedOWLAxiomListFrameSectionRow[Query]]]

  protected def initialiseOWLView(): Unit = {

    setLayout(GridBagLayout())
    val readMe =
      "<html>" +
        "<h1>Interactive Optimal Repair</h1>" +
        "<p>TBA</p>" +
        "</html>"
    add(breakingJLabel(readMe),
      GridBagConstraints()
        .coordinates(0,0)
        .anchor(GridBagConstraints.FIRST_LINE_START)
        .weight(1,0)
        .fill(GridBagConstraints.HORIZONTAL)
        .insets(32,32,32,32))

    val startButton = JButton("Start Assistant ...")
    startButton.setPreferredSize(Dimension(200,50))
    startButton.addActionListener(_ => startUserInteraction())
    add(startButton,
      GridBagConstraints()
        .coordinates(0, 1)
        .insets(32,0,0,0))

    add(JLabel(),
      GridBagConstraints()
        .coordinates(0,2)
        .weight(1,1)
        .fill(GridBagConstraints.BOTH))
  }

  private def startUserInteraction(): Unit = {
    val panel = JPanel(BorderLayout(16, 16))
    panel.add(breakingJLabel("Please wait while it is determined if the active ontology is supported..."), BorderLayout.NORTH)
    val pane = JOptionPane(panel)
    val dialog = pane.createDialog(InteractiveOptimalRepairViewComponent.this, "Interactive Optimal Repair")
    dialog.setResizable(true)
    dialog.setMinimumSize(Dimension(640, 480))
    val cancelButton = JButton("Cancel")
    cancelButton.addActionListener(_ => {
      cancelActiveWorkers()
      dialog.setVisible(false)
    })
    val nextButton = JButton("Next")
    nextButton.setEnabled(false)
    asynchronouslyInNewWorker {
      ELExpressivityChecker.check(getOWLModelManager().getActiveOntology())
    } executeAndThen {
      isSupported => {
        panel.removeAll()
        panel.add(breakingJLabel(if isSupported then "The active ontology is supported." else "The active ontology is currently not supported since it contains axioms not expressible in 𝓔𝓛.  A future version will widen support towards Horn-𝓐𝓛𝓒𝓡𝓞𝓘."), BorderLayout.NORTH)
        panel.revalidate()
        panel.repaint()

        if isSupported then {

          given owlEditorKit: OWLEditorKit = getOWLEditorKit()

          asynchronouslyInNewWorker {
            val terminology = getOWLModelManager.getOWLOntologyManager.createOntology(getOWLModelManager.getActiveOntology.getTBoxAxioms(Imports.INCLUDED))
            val terminologyReasoner = ElkReasonerFactory().createNonBufferingReasoner(terminology)
            terminologyReasoner.precomputeInferences()
            terminologyReasoner.flush()
            terminologyReasoner
          } inParallelWith asynchronouslyInNewWorker {
            val ontologyReasoner = ElkReasonerFactory().createNonBufferingReasoner(getOWLModelManager.getActiveOntology)
            ontologyReasoner.precomputeInferences()
            ontologyReasoner.flush()
            ontologyReasoner
          } executeAndThen {
            (terminologyReasoner, ontologyReasoner) => {
              nextButton.enableWithSingleActionListener(_ => {
                /* State 0: Repair Request */
                panel.removeAll()
                panel.add(breakingJLabel("Please specify the unwanted consequences for which the active ontology is to be repaired.  Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported.  Support will be extended towards Horn-𝓐𝓛𝓒𝓡𝓞𝓘 as well as concept inclusions (C SubClassOf: D) in a future version."), BorderLayout.NORTH)
                val repairRequestAxiomList: OrderedOWLAxiomList[Query] =
                  OrderedOWLAxiomList[Query]("Repair Request", "Unwanted Consequence",
                    () => OWLExpressionParserException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported.", 0, 0, false, false, false, false, false, false, Collections.emptySet),
                    ax => {
                      if !ELExpressivityChecker.checkAxiom(ax) then Some(OWLException("Currently only 𝓔𝓛 concept assertions (a Type: C) and role assertions (a Fact: r b) are supported."))
                      else if terminologyReasoner.isEntailed(ax) then Some(OWLException("Tautologies cannot be removed."))
                      else if !ontologyReasoner.isEntailed(ax) then Some(OWLException("The axiom is not entailed by the active ontology and thus need not be repaired for."))
                      else None
                    })
                panel.add(repairRequestAxiomList, BorderLayout.CENTER)
                panel.revalidate()
                panel.repaint()
                nextButton.enableWithSingleActionListener(_ => {
                  /* State 1: Interaction Strategy */
                  nextButton.setEnabled(false)
                  panel.removeAll()
                  terminologyReasoner.dispose()
                  ontologyReasoner.dispose()
                  val strategyRadioButtons = Strategy.values.map(s => (JRadioButton(s.toString), s)).toMap
                  strategyRadioButtons.foreach { case (button, Strategy.SMART) => button.setEnabled(false); case _ => {} }
                  val strategyRadioButtonGroup = ButtonGroup()
                  strategyRadioButtons.keys.foreach(strategyRadioButtonGroup.add)
                  val strategyRadioButtonPanel = JPanel()
                  strategyRadioButtonPanel.setLayout(BoxLayout(strategyRadioButtonPanel, BoxLayout.Y_AXIS))
                  strategyRadioButtons.keys.foreach(strategyRadioButtonPanel.add)
                  strategyRadioButtons.keys.foreach(b => b.addActionListener(_ => { if b.isSelected then nextButton.setEnabled(true) })) // should be moved below setting the action listener for very fast users
                  panel.add(breakingJLabel("Please select an interaction strategy."), BorderLayout.NORTH)
                  panel.add(strategyRadioButtonPanel, BorderLayout.CENTER)
                  panel.revalidate()
                  panel.repaint()
                  nextButton.setSingleActionListener(_ => {
                    /* State 2: User Interaction */
                    nextButton.setEnabled(false)

                    panel.removeAll()
                    val unwantedConsequences = repairRequestAxiomList.stream().toScala(LazyList)
                    val repairRequest = RepairRequest(unwantedConsequences: _*)
                    val strategy = strategyRadioButtons.keys.find(_.isSelected).map(strategyRadioButtons).get

                    given repairConfiguration: RepairConfiguration =
                      RepairConfiguration(ELExpressivityChecker.getELAxioms(getOWLModelManager.getActiveOntology).toSet, repairRequest)

                    asynchronouslyInNewWorker {
                      UserInteraction(strategy)
                    } executeAndThen { userInteraction =>

                      def lock(list: OrderedOWLAxiomList[Query]) = {
                        list.isEditable = false
                        list.refresh()
                      }

                      def unlock(list: OrderedOWLAxiomList[Query]) = {
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
                            asynchronouslyInNewWorker("Processing user answer ACCEPT to query " + query) {
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
                            asynchronouslyInNewWorker("Processing user answer IGNORE to query " + query) {
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
                            asynchronouslyInNewWorker("Processing user answer DECLINE to query " + query) {
                              userInteraction.receiveAnswer(query, DECLINE)
                            } executeAndThen { _ => unlock(list) }
                          })

                      val repairSeedInteractionAxiomList: OrderedOWLAxiomList[Query] =
                        new OrderedOWLAxiomList[Query]("Questions", "Question") {
                          override protected def getButtons(value: Object): java.util.List[MListButton] = {
                            value match
                              case classTag_OrderedOWLAxiomListFrameSectionRow_Query(row) if isEditable =>
                                strategy match
                                  case Strategy.FAST =>
                                    java.util.Collections.singletonList(
                                      newDeclineButton(this, row.getAxiom))
                                  case Strategy.SMART =>
                                    ???
                                  case Strategy.BEST =>
                                    java.util.List.of(
                                      newAcceptButton(this, row.getAxiom),
                                      newIgnoreButton(this, row.getAxiom),
                                      newDeclineButton(this, row.getAxiom))
                              case _ => Collections.emptyList()
                          }
                        }
                      repairSeedInteractionAxiomList.isEditable = true

                      val user = new User() {
                        override def showQuestion(query: Query): Unit =
                          invokeLaterOnProtegeThread { repairSeedInteractionAxiomList.add(query) }
                        override def removeQuestion(query: Query): Unit =
                          invokeLaterOnProtegeThread { repairSeedInteractionAxiomList.remove(query) }
                      }

                      panel.add(breakingJLabel("Please carefully assess each of the below axioms.  More specifically, please accept each valid axiom and decline each invalid axiom.  If you are unsure, you could also ignore some axioms, but then the repair might not be satisfactory.  After all questions have been considered, the induced optimal repair will be computed by clicking the below button."), BorderLayout.NORTH)
                      panel.add(repairSeedInteractionAxiomList, BorderLayout.CENTER)
                      panel.revalidate()
                      panel.repaint()

                      asynchronouslyInNewWorker("User interaction is running...") {
                        userInteraction.start(user)
                        while !userInteraction.hasBeenCompleted() do Thread.sleep(1000)
                        userInteraction.getRepairSeed()
                      } inParallelWith asynchronouslyInNewWorker("Checking if the input ontology is acyclic...") {
                        IQSaturation().isAcyclic
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

                            val compatibilityModeRadioButtons = CompatibilityMode.values.map(s => (JRadioButton(s.description), s)).toMap
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
                            queryLanguageRadioButtons.foreach { case (button, QueryLanguage.CQ) => button.setEnabled(false); case _ => {} }
                            nextButton.setEnabled(true)

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
                              asynchronouslyInNewWorker {
                                given ontologyManager: OWLOntologyManager = getOWLModelManager.getOWLOntologyManager
                                Repair(queryLanguage, repairSeed).compute(compatibilityMode)
                              } executeAndThen {
                                repair => {
                                  nextButton.enableWithSingleActionListener(_ => {
                                    /* State 5: All Tasks Finished */
                                    asynchronouslyInNewWorker {
                                      getOWLModelManager.getOWLOntologyManager.removeAxioms(getOWLModelManager.getActiveOntology, getOWLModelManager.getActiveOntology.getABoxAxioms(Imports.INCLUDED))
                                      getOWLModelManager.getOWLOntologyManager.addAxioms(getOWLModelManager.getActiveOntology, repair.getABoxAxioms(Imports.INCLUDED))
                                    } executeAndThen {
                                      _ =>
                                        panel.removeAll()
                                        dialog.setVisible(false)
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

        pane.setOptions(Array(cancelButton, nextButton))
        dialog.setVisible(true)
      }
    }
  }

  protected def disposeOWLView(): Unit = {
    cancelActiveWorkers()
  }

}
