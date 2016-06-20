/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._
import solvers._
import leon.utils.fixpoint

/** Preprocesses a problem by simplifying its spec */
case object SimplifySpec extends PreprocessingRule("Simplification") {
  override def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val sf = SolverFactory.getFromSettings(hctx, hctx.program).withTimeout(300)
    val s  = SimpleSolverAPI(sf)
    if (s.solveSAT(p.pc.toClause)._1.contains(false)) {
      Seq(solve(Solution.unreachable))
    } else {
      // We don't want evalGround...
      val simplifier = (simplifyLets _)
        .andThen(simplifyPaths(sf, p.pc))
        .andThen(simplifyArithmetic)
      val newPhi = fixpoint(simplifier, 5)(p.phi)
      (newPhi != p.phi).option(
        decomp(List(p.copy(phi = newPhi)), forward, "Simplify spec.")
      )
    }
  }
}
