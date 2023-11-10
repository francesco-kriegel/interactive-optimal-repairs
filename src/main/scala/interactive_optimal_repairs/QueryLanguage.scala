package de.tu_dresden.inf.lat
package interactive_optimal_repairs

import org.semanticweb.owlapi.model.{OWLClassAssertionAxiom, OWLObjectPropertyAssertionAxiom}

/* This type represents the supported query language, i.e., currently IRQ. */
type Query = OWLClassAssertionAxiom | OWLObjectPropertyAssertionAxiom

enum QueryLanguage {
  case IQ, IRQ, CQ
}