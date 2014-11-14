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
    val TopLevelAnds(clauses) = p.pc

    val guide = sctx.program.library.guide.get

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(`guide`, _), Seq(expr)) => expr
    }

    def simplify(e: Expr): Expr = {
      Simplifiers.forPathConditions(sctx.context, sctx.program)(e)
    }

    def doSubstitute(substs: Seq[(Expr, Expr)], e: Expr): Expr = {
      var res = e
      for (s <- substs) {
        res = postMap(Map(s).lift)(res)
      }
      res
    }

    val alts = guides.collect {
      case g @ IfExpr(c, thn, els) =>
        val sub1 = p.copy(pc = And(c, replace(Map(g -> thn), p.pc)))
        val sub2 = p.copy(pc = And(Not(c), replace(Map(g -> els), p.pc)))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(Or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
          case _ =>
            None
        }

        Some(RuleInstantiation.immediateDecomp(p, this, List(sub1, sub2), onSuccess, "Guided If-Split on '"+c+"'"))

      case m @ MatchExpr(scrut0, cs) =>
        
        val scrut = scrut0 match {
          case v : Variable => v
          case _ => Variable(FreshIdentifier("scrut", true).setType(scrut0.getType))
        }
        var pcSoFar: Expr = if (scrut == scrut0) BooleanLiteral(true) else Equals(scrut0, scrut)

        val subs = for (c <- cs) yield {
          
          //println("="*40)

          val localScrut = c.pattern.binder.map(Variable) getOrElse scrut
          //println("PC so far:")
          //println(replace(Map(scrut -> localScrut), pcSoFar))
          val scrutConstraint = if (localScrut == scrut) BooleanLiteral(true) else Equals(localScrut, scrut)
          val substs = patternSubstitutions(localScrut, c.pattern)
          
          //println("Pattern : " + c.pattern)
          //println("SUBST")
          //substs foreach println

          val cond = conditionForPattern(localScrut, c.pattern)
          //println("cond: " + cond)
          val g = c.theGuard.getOrElse(BooleanLiteral(true))
          val pc  = simplify(doSubstitute(substs, 
            And(Seq(
              scrutConstraint,
              replace(Map(scrut -> localScrut), pcSoFar),
              cond, 
              g, 
              replace(Map(m -> c.rhs), p.pc)
            ))
          ))
          //println("PC")
          //println(pc)

          val phi = doSubstitute(substs, p.phi) 
          val free = variablesOf(And(pc, phi)) -- p.xs
          val guardSafe = replaceFromIDs(mapForPattern(scrut, c.pattern),g)
          val condSafe = conditionForPattern(scrut, c.pattern)
          //println("GUARD SAFE:")
          //println(guardSafe)
          //println("="*40)
          pcSoFar = simplify(And(Not(And(condSafe, guardSafe)), pcSoFar))
          val asPrefix = p.as.filter(free)

          Problem(asPrefix ++ (free -- asPrefix), pc, phi, p.xs)
        }

        val onSuccess: List[Solution] => Option[Solution] = { subs =>
          val cases = for ((c, s) <- cs zip subs) yield {
            c match {
              case SimpleCase(c, rhs) => SimpleCase(c, s.term)
              case GuardedCase(c, g, rhs) => GuardedCase(c, g, s.term)
            }
          }

          Some(Solution(
            Or(subs.map(_.pre)), 
            subs.map(_.defs).foldLeft(Set[FunDef]())(_ ++ _), 
            Let(scrut.id, scrut0, MatchExpr(scrut, cases))
          ))
        }

        Some(RuleInstantiation.immediateDecomp(p, this, subs.toList, onSuccess, "Guided Match-Split"))

      case e =>
       None
    }

    alts.flatten
  }
}