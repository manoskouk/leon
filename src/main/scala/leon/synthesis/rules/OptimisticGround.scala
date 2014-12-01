/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

import solvers._

case object OptimisticGround extends Rule("Optimistic Ground") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    if (!p.as.isEmpty && !p.xs.isEmpty) {
      val res = new RuleInstantiation(p, this, SolutionBuilder.none, this.name, this.priority) {
        def apply(sctx: SynthesisContext) = {

          val solver = SimpleSolverAPI(sctx.fastSolverFactory) // Optimistic ground is given a simple solver (uninterpreted)

          val xss = p.xs.toSet
          val ass = p.as.toSet

          val tpe = TupleType(p.xs.map(_.getType))

          var i = 0;
          var maxTries = 3;

          var result: Option[RuleApplication] = None
          var continue                        = true
          var predicates: Seq[Expr]           = Seq()

          while (result.isEmpty && i < maxTries && continue) {
            val phi = andJoin(p.pc +: p.phi +: predicates)
            //println("SOLVING " + phi + " ...")
            solver.solveSAT(phi) match {
              case (Some(true), satModel) =>
                val satXsModel = satModel.filterKeys(xss) 

                val newPhi = valuateWithModelIn(phi, xss, satModel)

                //println("REFUTING " + Not(newPhi) + "...")
                solver.solveSAT(Not(newPhi)) match {
                  case (Some(true), invalidModel) =>
                    // Found as such as the xs break, refine predicates
                    predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

                  case (Some(false), _) =>
                    result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(satModel))))))

                  case _ =>
                    continue = false
                    result = None
                }

              case (Some(false), _) =>
                if (predicates.isEmpty) {
                  result = Some(RuleClosed(Solution(BooleanLiteral(false), Set(), Error(tpe, p.phi+" is UNSAT!"))))
                } else {
                  continue = false
                  result = None
                }
              case _ =>
                continue = false
                result = None
            }

            i += 1
          }

          result.getOrElse(RuleFailed())
        }
      }
      List(res)
    } else {
      Nil
    }
  }
}
