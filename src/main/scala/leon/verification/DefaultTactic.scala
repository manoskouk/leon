/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Definitions._
import purescala.Constructors._

import scala.collection.mutable.{Map => MutableMap}

class DefaultTactic(vctx: VerificationContext) extends Tactic(vctx) {
    val description = "Default verification condition generation approach"
    override val shortDescription = "default"

    def generatePostconditions(fd: FunDef): Seq[VerificationCondition] = {
      (fd.postcondition, fd.body) match {
        case (Some(post), Some(body)) =>
          val postCons = breakIfNeeded(application(post, Seq(body))) 
          postCons map { post => 
            val expr = implies(precOrTrue(fd), post)
            new VerificationCondition(expr, fd, VCPostcondition, this).setPos(post)
          }
        case _ =>
          Nil
      }
    }
  
    def generatePreconditions(fd: FunDef): Seq[VerificationCondition] = {
      fd.body match {
        case Some(body) =>
          val calls = collectWithPC {
            case c @ FunctionInvocation(tfd, _) if tfd.hasPrecondition => (c, tfd.precondition.get)
          }(body)

          calls.flatMap {
            case ((fi @ FunctionInvocation(tfd, args), pre), path) =>
              val pres  = breakIfNeeded(pre) 
              pres map { pre => 
                val pre2 = replaceFromIDs((tfd.params.map(_.id) zip args).toMap, pre)
                val vc = implies(and(precOrTrue(fd), path), pre2)
                new VerificationCondition(vc, fd, VCPrecondition, this).setPos(fi)
              }
          }

        case None =>
          Nil
      }
    }

    def generateCorrectnessConditions(fd: FunDef): Seq[VerificationCondition] = {
      fd.body match {
        case Some(body) =>
          val calls = collectWithPC {
            case e @ Error(_, "Match is non-exhaustive") =>
              (e, VCExhaustiveMatch, BooleanLiteral(false).setPos(e))

            case e @ Error(_, _) =>
              (e, VCAssert, BooleanLiteral(false).setPos(e))

            case a @ Assert(cond, Some(err), _) => 
              val kind = if (err.startsWith("Map ")) {
                VCMapUsage
              } else if (err.startsWith("Array ")) {
                VCArrayUsage
              } else {
                VCAssert
              }

              (a, kind, cond)
            case a @ Assert(cond, None, _) => (a, VCAssert, cond)
            // Only triggered for inner ensurings, general postconditions are handled by generatePostconditions
            case a @ Ensuring(body, post) => (a, VCAssert, application(post, Seq(body)).setPos(post))
          }(body)

          calls.flatMap {
            case ((e, kind, errorCond), path) =>
              val errorConds = breakIfNeeded(errorCond)
              errorConds map { errorCond =>
                val vc = implies(and(precOrTrue(fd), path), errorCond)
                new VerificationCondition(vc, fd, kind, this).setPos(errorCond)
              }
          }

        case None =>
          Nil
      }
    }
}
