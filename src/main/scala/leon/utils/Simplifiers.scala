package leon
package utils

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.ScopeSimplifier
import solvers.z3.UninterpretedZ3Solver
import solvers._

object Simplifiers {
  
  def bestEffort(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      removeWitnesses(p) _,
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      decomposeIfs _,
      matchToIfThenElse _,
      simplifyPaths(uninterpretedZ3)(_),
      patternMatchReconstruction _,
      rewriteTuples _,
      evalGround(ctx, p),
      normalizeExpression _
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    // Simplify first using stable simplifiers
    val s = fixpoint(simple, 5)(e)

    // Clean up ids/names
    (new ScopeSimplifier).transform(s)
  }

  // Besteffort, but keep witnesses
  def forPathConditions(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      decomposeIfs _,
      matchToIfThenElse _,
      simplifyPaths(uninterpretedZ3)(_),
      patternMatchReconstruction _,
      rewriteTuples _,
      evalGround(ctx, p),
      normalizeExpression _
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    fixpoint(simple, 5)(e)
  }

  def namePreservingBestEffort(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      decomposeIfs _,
      rewriteTuples _,
      evalGround(ctx, p),
      normalizeExpression _
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    // Simplify first using stable simplifiers
    fixpoint(simple, 5)(e)
  }
}
