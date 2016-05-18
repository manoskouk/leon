/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers.SolverFactory
import leon.utils.fixpoint
import purescala.ExprOps._

/** Preprocesses a problem by simplifying its spec */
case object SimplifySpec extends PreprocessingRule("Simplification") {
  override def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // We don't want evalGround...
    val simplifier = (simplifyLets _)
      .andThen(simplifyPaths(SolverFactory.getFromSettings(hctx, hctx.program), p.pc))
      .andThen(simplifyArithmetic)
    val newPhi = fixpoint(simplifier, 5)(p.phi)
    (newPhi != p.phi).option(
      decomp(List(p.copy(phi = newPhi)), forward, "Simplify spec.")
    )
  }
}
