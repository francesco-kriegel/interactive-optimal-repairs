package de.tu_dresden.inf.lat
package protege_components

import protege_components.Util.*

import org.phenoscape.scowl.*
import org.protege.editor.owl.model.OWLModelManager
import org.protege.editor.owl.model.classexpression.OWLExpressionParserException
import org.protege.editor.owl.model.parser.{ParserUtil, ProtegeOWLEntityChecker}
import org.protege.editor.owl.ui.clsdescriptioneditor.OWLExpressionChecker
import org.semanticweb.owlapi.manchestersyntax.parser.ManchesterOWLSyntaxParserImpl
import org.semanticweb.owlapi.manchestersyntax.renderer.ParserException
import org.semanticweb.owlapi.model.{OWLAxiom, OWLOntologyLoaderConfiguration}

import java.util
import java.util.Collections
import scala.reflect.{ClassTag, classTag}

class OWLAxiomChecker[Ax <: OWLAxiom : ClassTag](private val mngr: OWLModelManager, unexpectedAxiomException: () => OWLExpressionParserException = () => OWLExpressionParserException("Expected an OWL axiom", 0, 0, false, false, false, false, false, false, Collections.emptySet)) extends OWLExpressionChecker[Ax] {

  @throws[OWLExpressionParserException]
  override def check(text: String): Unit = {
    this.createObject(text)
  }

  @throws[OWLExpressionParserException]
  override def createObject(text: String): Ax = {
    if text contains "Fact:" then {
      def newParserException() = OWLExpressionParserException("Expected an OWL object property assertion axiom of the form 'subject Fact: property object'.", 0, 0, false, false, false, false, false, false, Collections.emptySet)
      val ttext = text.trim
      val i = ttext.indexOf("Fact:")
      val subjectText = ttext.substring(0, i).trim
      val factText = ttext.substring(i + 5).trim
      if factText contains " " then
        val splitFactText = factText.trim.split(' ')
        val propertyText = splitFactText(0).trim
        val objectText = splitFactText(1).trim
        val finder = ProtegeOWLEntityChecker(this.mngr.getOWLEntityFinder)
        val s = finder.getOWLIndividual(subjectText)
        if s == null then throw newParserException()
        val p = finder.getOWLObjectProperty(propertyText)
        if p == null then throw newParserException()
        val o = finder.getOWLIndividual(objectText)
        if o == null then throw newParserException()
        val ax = s Fact (p, o)
//        if (ax.isInstanceOf[Ax]) ax.asInstanceOf[Ax]
        if (classTag[Ax].runtimeClass.isInstance(ax)) ax.asInstanceOf[Ax]
        else throw unexpectedAxiomException()
      else
        throw throw newParserException()
    } else {
      val parser = ManchesterOWLSyntaxParserImpl(() => OWLOntologyLoaderConfiguration(), this.mngr.getOWLDataFactory)
      parser.setOWLEntityChecker(ProtegeOWLEntityChecker(this.mngr.getOWLEntityFinder))
      parser.setStringToParse(text)
      try
        val ax = parser.parseAxiom
//        if ax.isInstanceOf[Ax] then ax.asInstanceOf[Ax]
        if (classTag[Ax].runtimeClass.isInstance(ax)) ax.asInstanceOf[Ax]
        else throw unexpectedAxiomException()
      catch
        case var4: ParserException => throw ParserUtil.convertException(var4)
    }
  }

}
