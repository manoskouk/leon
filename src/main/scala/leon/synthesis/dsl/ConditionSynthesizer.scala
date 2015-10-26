/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package dsl

import purescala.Extractors._
import purescala.Types._
import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.DefOps.replaceFunDefs

import rules.CEGIS

import solvers._
import leon.evaluators._

import grammars.ValueGrammar
import bonsai.enumerators._

class ConditionSynthesizer(
  ctx: LeonContext,
  program: Program,
  val c: Conditionally,
  val fd: FunDef
) {

  private type Alt = Expr
  private type Assignment = Set[Alt]

  private val settings = SynthesisPhase.processOptions(ctx)//.copy(rules = Seq(CEGIS))

  private case class ExamplesAssignment(esToAlts: Map[InExample, Assignment]) {

    def isViable = esToAlts.values.forall(_.nonEmpty)

    def unique(alt: Alt) = esToAlts.collect {
      case (ex, alts) if alts == Set(alt) => ex
    }.toSeq

    def incompatibleWith(alt: Alt) = esToAlts.collect {
      case (ex, alts) if !alts.contains(alt) => ex
    }.toSeq

    def compatibleWith(alt: Alt) = esToAlts.collect {
      case (ex, alts) if alts.contains(alt) => ex
    }.toSeq

    def bank(alt: Alt) = ExamplesBank(
      unique(alt)           map (in => InOutExample(in.ins, Seq(BooleanLiteral(true )))),
      incompatibleWith(alt) map (in => InOutExample(in.ins, Seq(BooleanLiteral(false))))
    )

    def removeAlt(alt: Alt) = ExamplesAssignment(esToAlts.mapValues(_ - alt))

  }

  val pc = pcOf(c, fd.fullBody)

  private lazy val initExamples: ExamplesAssignment = {

    val evaluator = new AngelicEvaluator(new StreamEvaluator(ctx, program))

    def inputToExamples(es: Seq[Expr]): Set[Alt] = {
      def checkAlt(alt: Alt, realArgs: Seq[Expr]) = {
        evaluator.compile(alt, fd.paramIds).exists { evalFun =>
          evalFun(new Model((fd.paramIds zip realArgs).toMap)) match {
            case EvaluationResults.Successful(out) =>
              true
            case _ =>
              false
          }
        }
      }
      c.alts.toSet.filter(checkAlt(_, es))
    }

    val maxEnumerated = 100
    val maxValid      = 40
    val enum   = new MemoizedEnumerator[TypeTree, Expr](ValueGrammar.getProductions(_)(ctx))
    val inputs = enum.iterator(tupleTypeWrap(fd.params map { _.getType })).map(unwrapTuple(_, fd.params.size))
    val filtering: Seq[Expr] => Boolean = { es =>
      evaluator.eval(andJoin(pc), fd.paramIds.zip(es).toMap) match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          true
        case _ =>
          false
      }
    }
    val results = inputs.take(maxEnumerated)
      .filter(filtering)
      .take(maxValid)
      .map(es => InExample(es) -> inputToExamples(es))
      .toMap

    //results.keys foreach { ex =>
    //  println(ex.ins.mkString("\t"))
    //}

    ExamplesAssignment(results)

  }

  private val primChooses = {
    val correctnessConds = {
      val sf = SolverFactory.getFromSettings(ctx, program)
      c.alts map { alt =>
        val cc = simpleCorrectnessCond(alt, pc, sf)
        val post = application(fd.postOrTrue, Seq(alt))
        //println(alt + " ~~~~~>")
        //println(s"  $cc")
        //println(s"  $post")
        and(cc, post)
      }
    }

    c.alts.zipWithIndex.map{ case (alt, ind) =>
      val cond = FreshIdentifier("cond", BooleanType, alwaysShowUniqueID = true)
      val index = c.alts.indexOf(alt)
      Choose(Lambda(Seq(ValDef(cond)), and(
        implies(     cond.toVariable,  correctnessConds(index)),
        implies( not(cond.toVariable), orJoin(correctnessConds.drop(index+1)))
      )))
    }
  }

  private val chooseFd = {
    val newFd = fd.duplicate()
    val newE = c.alts.zip(primChooses).foldRight[Expr](Error(c.alts.head.getType, "")) {
      case ((alt, ch), rest) =>
        IfExpr(ch, alt, rest)
    }
    newFd.fullBody = replace(Map(c -> newE), newFd.fullBody)
    newFd
  }

  private val (chooseProg, fMap) = replaceFunDefs(program){
    case `fd` =>
      Some(chooseFd)
    case _ =>
      None
  }

  private def solveAlt(alt: Alt, ch: Choose, es: ExamplesAssignment) = {
    val pc = pcOf(ch, chooseFd.fullBody)
    val info = SourceInfo(chooseFd, andJoin(pc), ch, ch.pred, es.bank(alt))
    val synthesizer = new Synthesizer(ctx, chooseProg, info, settings)
    val sol = synthesizer.synthesize()._2.headOption
    synthesizer.shutdown()
    sol
  }

  def solve() = {

    val chooses = primChooses.map( preMap {
      case FunctionInvocation(TypedFunDef(fd, tps), args) =>
        Some(FunctionInvocation(TypedFunDef(fMap.getOrElse(fd, fd), tps), args))
      case _ =>
        None
    }).map(_.asInstanceOf[Choose])

    c.alts.zip(chooses).foldLeft(initExamples) { case (es, (alt, ch)) =>
      val e = solveAlt(alt, ch, es).map(_.toExpr).getOrElse(
        ctx.reporter.fatalError(s"Failed! Best I could do:\n$chooseFd")
      )
      chooseFd.fullBody = replace(Map(ch -> e), chooseFd.fullBody)
      es.removeAlt(alt)
    }

    ctx.reporter.info(s"Success!\n$chooseFd")

  }

}

