/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils.Simplifiers

import purescala.Trees._
import purescala.Definitions._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

import solvers._

case object GuidedDecomp extends Rule("Guided Decomp") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(clauses) = p.ws

    val guide = sctx.program.library.guide.get

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(`guide`, _), Seq(expr)) => expr
    }

    val simplify = Simplifiers.bestEffort(sctx.context, sctx.program)_

    def doSubstitute(substs: Seq[(Expr, Expr)], e: Expr): Expr = {
      var res = e
      for (s <- substs) {
        res = postMap(Map(s).lift)(res)
      }
      res
    }

    val alts = guides.collect {
      case g @ IfExpr(c, thn, els) =>
        val sub1 = p.copy(ws = replace(Map(g -> thn), p.ws), pc = and(c, replace(Map(g -> thn), p.pc)))
        val sub2 = p.copy(ws = replace(Map(g -> els), p.ws), pc = and(Not(c), replace(Map(g -> els), p.pc)))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(sub1, sub2), onSuccess, "Guided If-Split on '"+c+"'"))

      case m @ MatchExpr(scrut0, cs) =>

        val scrut = scrut0 match {
          case v : Variable => v
          case _ => Variable(FreshIdentifier("scrut", true).setType(scrut0.getType))
        }
        var scrutCond: Expr = if (scrut == scrut0) BooleanLiteral(true) else Equals(scrut0, scrut)

        val subs = for ((c, cond) <- cs zip matchCasePathConditions(m, List(p.pc))) yield {
          
          val localScrut = c.pattern.binder.map(Variable) getOrElse scrut
          val scrutConstraint = if (localScrut == scrut) BooleanLiteral(true) else Equals(localScrut, scrut)
          val substs = patternSubstitutions(localScrut, c.pattern)
          
          val pc  = simplify(and(
            scrutCond,
            replace(Map(scrut0 -> scrut), doSubstitute(substs,scrutConstraint)),
            replace(Map(scrut0 -> scrut), replace(Map(m -> c.rhs), andJoin(cond)))
          ))
          val ws = replace(Map(m -> c.rhs), p.ws)
          val phi = doSubstitute(substs, p.phi)
          val free = variablesOf(and(pc, phi)) -- p.xs
          val asPrefix = p.as.filter(free)

          Problem(asPrefix ++ (free -- asPrefix), ws, pc, phi, p.xs)
        }

        val onSuccess: List[Solution] => Option[Solution] = { subs =>
          val cases = for ((c, s) <- cs zip subs) yield {
            c.copy(rhs = s.term)
          }

          Some(Solution(
            orJoin(subs.map(_.pre)),
            subs.map(_.defs).foldLeft(Set[FunDef]())(_ ++ _),
            if (scrut0 != scrut) Let(scrut.id, scrut0, matchExpr(scrut, cases))
            else matchExpr(scrut, cases)
          ))
        }

        Some(RuleInstantiation.immediateDecomp(p, this, subs.toList, onSuccess, "Guided Match-Split"))

      case e =>
       None
    }

    alts.flatten
  }
}
