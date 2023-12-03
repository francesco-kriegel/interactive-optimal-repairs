/*-
 * #%L
 * Protégé Extensions
 * %%
 * Copyright (C) 2020 Francesco Kriegel
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package de.tu_dresden.inf.lat
package protege_components

import java.awt.event.ActionListener
import java.awt.{BorderLayout, Dimension, GridBagConstraints, Insets}
import java.lang.reflect.InvocationTargetException
import javax.swing.*

object Util {

  private def runOnProtegeThread(runnable: Runnable, sync: Boolean): Unit = {
    if (SwingUtilities.isEventDispatchThread) {
      runnable.run()
    } else {
      try {
        if (sync)
          SwingUtilities.invokeAndWait(runnable)
        else
          SwingUtilities.invokeLater(runnable)
      } catch {
        case e: Error =>
          if (e.getMessage.equals("Cannot call invokeAndWait from the event dispatcher thread")) {
            runnable.run()
          } else throw RuntimeException(e)
        case e @ (_: InvocationTargetException | _: InterruptedException) => throw RuntimeException(e)
      }
    }
  }

  def synchronouslyOnProtegeThread(code: => Unit): Unit = {
    runOnProtegeThread(() => code, true)
  }

  def asynchronouslyOnProtegeThread(code: => Unit): Unit = {
    runOnProtegeThread(() => code, false)
  }

  def invokeLaterOnProtegeThread(code: => Unit): Unit = {
    SwingUtilities.invokeLater(() => { code })
  }

  extension(c: GridBagConstraints) {
    def coordinates(gridx: Int, gridy: Int): GridBagConstraints = { c.gridx = gridx; c.gridy = gridy; c }
    def span(gridwidth: Int, gridheight: Int): GridBagConstraints = { c.gridwidth = gridwidth; c.gridheight = gridheight; c }
    def weight(weightx: Int, weighty: Int): GridBagConstraints = { c.weightx = weightx; c.weighty = weighty; c }
    def anchor(anchor: Int): GridBagConstraints = { c.anchor = anchor; c }
    def fill(fill: Int): GridBagConstraints = { c.fill = fill; c }
    def insets(top: Int, left: Int, bottom: Int, right: Int): GridBagConstraints = { c.insets = Insets(top, left, bottom, right); c }
    def pad(ipadx: Int, ipady: Int): GridBagConstraints = { c.ipadx = ipadx; c.ipady = ipady; c }
  }

  def htmlParagraph(text: String): String = "<html><p>" + text + "</p></html>"

  def breakingJLabelInJPanel(text: String): (JPanel, JLabel) = {
    // put a label into a panel with border layout to enable automatic line breaks
    val label = JLabel(if text contains "<html>" then text else htmlParagraph(text))
    label.setVerticalTextPosition(SwingConstants.TOP)
    label.setHorizontalTextPosition(SwingConstants.LEFT)
    val panel = JPanel(BorderLayout())
    panel.add(label, BorderLayout.NORTH)
    (panel, label)
  }

  def breakingJLabel(text: String): JPanel = {
    breakingJLabelInJPanel(text)._1
  }

  def asHTMLMessage(msg: String): String = {
    "<html><body>"
      + msg.replace("\n", "<br>")
      .replace("\t", "&nbsp;&nbsp;&nbsp;&nbsp;")
      + "</body></html>"
  }

  extension(button: AbstractButton) {
    def removeAllActionListeners(): Unit = {
      button.getActionListeners.foreach(button.removeActionListener)
    }
    def setSingleActionListener(l: ActionListener): Unit = {
      removeAllActionListeners()
      button.addActionListener(l)
    }
    def enableWithSingleActionListener(l: ActionListener): Unit = {
      setSingleActionListener(l)
      button.setEnabled(true)
    }
    def enableWithSingleAction(code: => Unit): Unit = {
      enableWithSingleActionListener(_ => { code })
    }

    def setFixedSize(size: Dimension): Unit = {
      button.setMinimumSize(size)
      button.setPreferredSize(size)
      button.setMaximumSize(size)
    }
  }

  extension(container: java.awt.Container) {
    def _add(comp: java.awt.Component): java.awt.Container = {
      container.add(comp)
      container
    }

    def _add(comp: java.awt.Component, constraints: AnyRef): java.awt.Container = {
      container.add(comp, constraints)
      container
    }
  }

}
