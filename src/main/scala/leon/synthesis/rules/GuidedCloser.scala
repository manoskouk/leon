/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

import solvers._

case object GuidedCloser extends NormalizingRule("Guided Closer") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = p.pc

    val guide = sctx.program.library.guide.get

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(`guide`, _), Seq(expr)) => expr
    }

    val alts = guides.flatMap { e =>
      // Tentative solution using e
      val wrappedE = if (p.xs.size == 1) Tuple(Seq(e)) else e

      val vc = And(p.pc, LetTuple(p.xs, wrappedE, Not(p.phi)))

      val solver = sctx.newSolver.setTimeout(1000L)

      solver.assertCnstr(vc)
      val osol = solver.check match {
        case Some(false) =>
          Some(Solution(BooleanLiteral(true), Set(), wrappedE, true))

        case None =>
          Some(Solution(BooleanLiteral(true), Set(), wrappedE, false))

        case _ =>
          None
      }

      osol.map { s =>
        RuleInstantiation.immediateSuccess(p, this, s)
      }
    }

    alts
  }
}
