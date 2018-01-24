/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import evaluators._
import leon.grammars._
import leon.grammars.enumerators._
import leon.grammars.enumerators.CandidateScorer.MeetsSpec
import leon.utils.DebugSectionSynthesisVerbose
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Common.Identifier
import purescala.Definitions._
import utils.MutableExpr
import solvers._

abstract class ProbDrivenEnumerationLike(name: String) extends Rule(name){
  case class Params(lab: Label, grammar: ExpressionGrammar, indistinguish: Boolean)
  def getParams(sctx: SynthesisContext, p: Problem): Params

  private case object UnsatPCException extends Exception("Unsat. PC")

  class NonDeterministicProgram(
    outerCtx: SearchContext,
    outerP: Problem
  ) {
    val timers = outerCtx.timers.synthesis.applications.get("Prob. driven enum")

    outerCtx.timers.synthesis

    import outerCtx.reporter._

    val solverTo = 5000

    val isByExample = outerP.phi.isInstanceOf[Passes]

    val outerExamples = {
      // Get from the params of the outer program if we are applying ind. heuristic
      val Params(_, _, indistinguish) = getParams(outerCtx, outerP)
      // If we do, we have to limit # of examples for performance
      val howMany = if (indistinguish) 3 else 50
      val fromProblem = outerP.qebFiltered(outerCtx).eb.examples
      val (in, inOut) = fromProblem.partition(_.isInstanceOf[InExample])
      //println(fromProblem)
      // We are forced to take all in-out examples
      if (inOut.nonEmpty) {
        if (isByExample) inOut
        else inOut ++ in.take(howMany - inOut.size)
      } else if (in.nonEmpty) in.take(howMany)
      else {
        // If we have none, generate one with the solver
        val solverF = SolverFactory.getFromSettings(outerCtx, outerCtx.program).withTimeout(solverTo)
        val solver  = solverF.getNewSolver()
        try {
          solver.assertCnstr(outerP.pc.toClause)
          solver.check match {
            case Some(true) =>
              val model = solver.getModel
              Seq(InExample(outerP.as map (id => model.getOrElse(id, simplestValue(id.getType)))))
            case None =>
              warning("Could not solve path condition")
              Seq(InExample(outerP.as.map(_.getType) map simplestValue))
            case Some(false) =>
              warning("PC is not satisfiable.")
              throw UnsatPCException
          }
        } finally {
          solverF.reclaim(solver)
        }
      }
    }

    //println("Final examples:")
    //println(outerExamples)


    // Create a fresh solution function with the best solution around the
    // current STE as body
    timers.transProg.start()

    val fd = outerCtx.functionContext.duplicate()
    def outerToInner(e: Expr) = preMap {
      case FunctionInvocation(TypedFunDef(fd1, tps), args) if fd1 == outerCtx.functionContext =>
        Some(FunctionInvocation(TypedFunDef(fd, tps), args))
      case _ => None
    }(e)
    def innerToOuter(e: Expr) = preMap {
      case FunctionInvocation(TypedFunDef(fd1, tps), args) if fd1 == fd =>
        Some(FunctionInvocation(TypedFunDef(outerCtx.functionContext, tps), args))
      case _ => None
    }(e)
    locally {
      fd.fullBody = postMap {
        case src if src eq outerCtx.source =>
          val body = new PartialSolution(outerCtx.search.strat, true)(outerCtx)
            .solutionAround(outerCtx.currentNode)(MutableExpr(NoTree(outerP.outType)))
            .getOrElse(fatalError("Unable to get outer solution"))
            .term

          Some(body)
        case _ =>
          None
      }(fd.fullBody)

      fd.fullBody = outerToInner(fd.fullBody)
    }

    val solutionBox = collect[MutableExpr] {
      case me: MutableExpr => Set(me)
      case _ => Set()
    }(fd.fullBody).head

    val program = { // FIXME: TERRIBLE HACK!!! Also breaks compatibility with class invariants
      val outerProgram = outerCtx.program
      Program {
        outerProgram.units.map { u =>
          if (!u.isMainUnit) u else {
            u.copy(defs = u.defs.map {
              case m: ModuleDef =>
                m.copy(defs = m.defs.map {
                  case cd: ClassDef => cd
                  case fd1: FunDef if fd1 == outerCtx.functionContext =>
                    fd
                  case fd1: FunDef =>
                    fd1.fullBody = outerToInner(fd1.fullBody)
                    fd1
                })
              case other => other
            })
          }
        }
      }
    }
    timers.transProg.stop()

    // It should be set to the solution you want to check at each time.
    // Usually it will either be cExpr or a concrete solution.
    private def setSolution(e: Expr) = solutionBox.underlying = e

    implicit val sctx = new SynthesisContext(outerCtx, outerCtx.settings, fd, program) // FIXME: .settings might need changing

    val p = {
      implicit val bindings = Map[Identifier, Identifier]()

      Problem(
        as = outerP.as,
        ws = outerToInner(outerP.ws),
        pc = outerP.pc.map(outerToInner),
        phi = outerToInner(outerP.phi),
        xs = outerP.xs,
        eb = ExamplesBank(outerExamples map (_.map(outerToInner)), Seq())
      )
    }
    var examples = p.eb.examples

    private val spec = letTuple(p.xs, solutionBox, p.phi)

    val useOptTimeout = sctx.findOptionOrDefault(SynthesisPhase.optUntrusted)
    // Limit prob. programs
    val (minLogProb, maxEnumerated) = {
      import SynthesisPhase._
      if (sctx.findOptionOrDefault(optMode) == Modes.ProbwiseOnly)
        (-1000000000.0, 100000000) // Run forever in probwise-only mode
      else
        (-50.0, 1000)
    }

    // How much deeper to seek when found an untrusted solution
    val untrustedCostRatio = 5

    val fullEvaluator = new TableEvaluator(sctx, program)
    val partialEvaluator = new PartialExpansionEvaluator(sctx, program)
    val solverF = SolverFactory.getFromSettings(sctx, program).withTimeout(solverTo)
    val Params(topLabel, grammar, indistinguish) = getParams(sctx, p)
    debug("Examples:\n" + examples.map(_.asString).mkString("\n"))

    // Evaluates a candidate against an example in the correct environment
    def evalCandidate(expr: Expr, evalr: Evaluator)(ex: Example): evalr.EvaluationResult = timers.eval.timed {
      setSolution(expr)

      def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
        case ((id, v), bd) => Let(id, v, bd)
      }

      val testExpr = ex match {
        case InExample(_) =>
          spec
        case InOutExample(_, outs) =>
          equality(expr, tupleWrap(outs))
      }

      evalr.eval(withBindings(testExpr), p.as.zip(ex.ins).toMap)
    }

    // Tests a candidate solution against an example in the correct environment
    def testCandidate(expr: Expr)(ex: Example): Option[Boolean] = {
      evalCandidate(expr, fullEvaluator)(ex) match {
        case EvaluationResults.Successful(value) =>
          val res = value == BooleanLiteral(true)
          if (!res) {
            debug(s"Negative result. Failing: $ex")
          }
          Some(res)
        case EvaluationResults.RuntimeError(err) =>
          debug(s"RE testing CE: $err")
          debug(s"  Failing example: $ex")
          debug(s"  Rejecting $expr")
          Some(false)
        case EvaluationResults.EvaluatorError(err) =>
          debug(s"Error testing CE: $err")
          debug(s"  Removing $ex")
          examples = examples diff Seq(ex)
          None
      }
    }

    private class NoRecEvaluator(sctx: SynthesisContext, pgm: Program) extends TableEvaluator(sctx, pgm) {
      override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
        case MutableExpr(_) =>
          throw EvalError("Trying to normalize based on rec. call body")
        case other => super.e(other)
      }
    }

    private val noRecEvaluator = new NoRecEvaluator(sctx, program)

    // Do not set the solution to expr
    def rawEvalCandidate(expr: Expr, ex: Example): EvaluationResults.Result[Expr] = {
      def withBindings(e: Expr) = p.pc.bindings.foldRight(e) {
        case ((id, v), bd) => let(id, v, bd)
      }

      val res = noRecEvaluator.eval(withBindings(expr), p.as.zip(ex.ins).toMap)
      // res match {
      //   case EvaluationResults.Successful(value) =>
      //   case EvaluationResults.RuntimeError(err) =>
      //     debug(s"RE testing CE: $err")
      //     debug(s"  Failing example: $ex")
      //   case EvaluationResults.EvaluatorError(err) =>
      //     debug(s"Error testing CE: $err")
      // }

      res
    }

    def partialTestCandidate(expansion: Expansion[Label, Expr], ex: Example): MeetsSpec.MeetsSpec = {
      val expr = ExpansionExpr(expansion)
      val res = evalCandidate(expr, partialEvaluator)(ex)
      res match {
        case EvaluationResults.Successful(BooleanLiteral(true)) => MeetsSpec.YES
        case EvaluationResults.Successful(BooleanLiteral(false)) => MeetsSpec.NO
        case EvaluationResults.Successful(_) => MeetsSpec.NOTYET
        case EvaluationResults.RuntimeError(_) => MeetsSpec.NO
        case EvaluationResults.EvaluatorError(_) => MeetsSpec.NOTYET
      }
    }

    def mkEnum = {
      val scorer = new CandidateScorer[Label, Expr](partialTestCandidate, _ => examples)
      new ProbwiseTopdownEnumerator(
        grammar, topLabel, scorer, examples, rawEvalCandidate,
        minLogProb, maxEnumerated, untrustedCostRatio, indistinguish
      )
    }.iterator(topLabel)

    var it = mkEnum

    debug("Root label: " + topLabel)
    debug("Grammar:")(DebugSectionSynthesisVerbose)
    debug(grammar.asString)(DebugSectionSynthesisVerbose)

    /**
      * Second phase of STE: verify a given candidate by looking for CEX inputs.
      * Returns the potential solution and whether it is to be trusted.
      */
    def validateCandidate(expr: Expr): Option[Solution] = {
      timers.validate.start()
      debug(s"Validating $expr")
      val solver = solverF.getNewSolver()

      try {
        setSolution(expr)
        solver.assertCnstr(p.pc and not(spec))
        solver.check match {
          case Some(true) =>
            // Found counterexample! Exclude this program
            val model = solver.getModel
            val cex = InExample(p.as.map(a => model.getOrElse(a, simplestValue(a.getType))))
            debug(s"Found cex $cex for $expr")
            examples +:= cex
            timers.cegisIter.stop()
            timers.cegisIter.start()
            if (indistinguish) {
              debug("Restarting enum...")
              it = mkEnum
            }
            None

          case Some(false) =>
            debug("Proven correct!")
            timers.cegisIter.stop()
            Some(Solution(BooleanLiteral(true), Set(), expr, isTrusted = true))

          case None =>
            if (useOptTimeout) {
              debug("Leon could not prove the validity of the resulting expression")
              // Interpret timeout in CE search as "the candidate is valid"
              Some(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false))
            } else {
              // TODO: Make STE fail early when it times out when verifying 1 program?
              None
            }
        }
      } finally {
        timers.validate.stop()
        solverF.reclaim(solver)
      }
    }

    def solutionStream: Stream[Solution] = {
      timers.cegisIter.start()
      var untrusted: Seq[Solution] = Seq()
      while (!sctx.interruptManager.isInterrupted && it.hasNext) {
        val expr = it.next
        debug(s"Testing: $expr")
        // FIXME: Testing should always succeed at this point
        if (examples.exists(testCandidate(expr)(_).contains(false))) {
          debug(s"Failed testing!")
        } else {
          debug(s"Passed testing!")
          validateCandidate(expr) foreach { sol =>
            val outerSol = sol.copy(term = innerToOuter(sol.term))
            if (sol.isTrusted) {
              // FIXME!!! TERRIBLE HACK
              outerCtx.program.definedFunctions.foreach { f =>
                f.fullBody = innerToOuter(f.fullBody)
              }
              return Stream(outerSol)
            } // Found verifiable solution, return immediately
            else {
              // Solution was not verifiable, remember it anyway.
              untrusted :+= outerSol
            }
          }
        }
      }
      // FIXME!!! TERRIBLE HACK
      outerCtx.program.definedFunctions.foreach { f =>
        f.fullBody = innerToOuter(f.fullBody)
      }

      untrusted.toStream // Best we could do is find unverifiable solutions
    }

  }

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    List(new RuleInstantiation(s"$name") {
      def apply(hctx: SearchContext): RuleApplication = {
        try {
          val ndProgram = new NonDeterministicProgram(hctx, p)
          RuleClosed(ndProgram.solutionStream)
        } catch {
          case UnsatPCException =>
            RuleClosed(Solution.UNSAT(p))
        }
      }
    })
  }
}

object ProbDrivenEnumeration extends ProbDrivenEnumerationLike("Prob. driven enum") {
  import leon.grammars.Tags
  import leon.grammars.aspects._
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val useTags   = sctx.findOptionOrDefault(SynthesisPhase.optProbwiseTags)
    val rootLabel = Label(p.outType).withAspect(TypeDepthBound(3))
    Params(
      if (useTags) rootLabel.withAspect(Tagged(Tags.Top, 0, None)) else rootLabel,
      grammars.default(sctx, p),
      sctx.findOptionOrDefault(SynthesisPhase.optProbwiseTopdownOpt)
    )
  }
}

object ProbDrivenSimilarTermEnumeration extends ProbDrivenEnumerationLike("Prob. driven similar term enum.") {
  import purescala.Extractors.TopLevelAnds
  import leon.grammars.aspects._
  import Witnesses.Guide
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val TopLevelAnds(clauses) = p.ws
    val guides = clauses.collect { case Guide(e) => e }
    Params(
      Label(p.outType).withAspect(SimilarTo(guides, sctx.functionContext)),
      grammars.default(sctx, p, guides),
      indistinguish = false
    )
  }
}