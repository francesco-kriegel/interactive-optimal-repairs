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

import org.protege.editor.core.ui.list.MListButton

import java.awt.event.ActionListener
import java.awt.{Color, Font, Graphics2D}

class TextMListButton(tooltipText: String, rollOverColor: Color, buttonText: String, buttonTextSize: Int, listener: ActionListener)
  extends MListButton(tooltipText: String, rollOverColor: Color, listener: ActionListener) {

  /**
   * The code of this method is copied and slightly modified from the class
   * org.exquisite.protege.ui.buttons.UnicodeButton in the Ontology Debugger Plugin for Protégé
   * @see https://git-ainf.aau.at/interactive-KB-debugging/debugger/blob/4a2e4c8ee36a8f63bf7facd099021420b0621cc9/protege-plugin/src/main/java/org/exquisite/protege/ui/buttons/UnicodeButton.java
   */
  override def paintButtonContent(g: Graphics2D): Unit = {
    g.setColor(Color.WHITE)
    g.setFont(new Font(Font.SANS_SERIF, Font.BOLD, buttonTextSize))
    val stringWidth = g.getFontMetrics().getStringBounds(buttonText, g).getBounds.width
    val w = getBounds.width
    val h = getBounds.height
    g.drawString(
      buttonText,
      getBounds.x + w / 2 - stringWidth / 2,
      getBounds.y + g.getFontMetrics().getAscent / 2 + h / 2 - 2)
  }

  override protected def getSizeMultiple: Int = { 4 }

}
