/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package repair

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.DefOps._
import purescala.Constructors._
import purescala.ScalaPrinter
import evaluators._
import solvers._
import utils._
import solvers.z3._
import codegen._
import verification._
import synthesis._
import synthesis.rules._
import synthesis.heuristics._
import synthesis.Witnesses._
import graph.DotGenerator
import leon.utils.ASCIIHelpers.title

class Repairman(ctx: LeonContext, initProgram: Program, fd: FunDef, verifTimeoutMs: Option[Long]) {
  val reporter = ctx.reporter

  var program = initProgram

  implicit val debugSection = DebugSectionRepair

  def repair() = {
    reporter.info(ASCIIHelpers.title("1. Discovering tests for "+fd.id))
    val t1 = new Timer().start
    val (passingTests, failingTests) = discoverTests

    reporter.info(f" - Passing: ${passingTests.size}%3d")
    reporter.info(f" - Failing: ${failingTests.size}%3d")

    reporter.info("Finished in "+t1.stop+"ms")


    reporter.info(ASCIIHelpers.title("2. Locating/Focusing synthesis problem"))
    val t2          = new Timer().start
    val (synth, ci) = getSynthesizer(passingTests, failingTests)
    val p           = synth.problem

    var solutions = List[Solution]()

    reporter.info("Finished in "+t2.stop+"ms")
    reporter.info(ASCIIHelpers.title("3. Synthesizing"))
    reporter.info(p)


    synth.synthesize() match {
      case (search, sols) =>
        for (sol <- sols) {

          // Validate solution if not trusted
          if (!sol.isTrusted) {
            reporter.info("Found untrusted solution! Verifying...")
            val (npr, fds) = synth.solutionToProgram(sol)

            getVerificationCounterExamples(fds.head, npr) match {
              case Some(ces) =>
                reporter.error("I ended up finding this counter example:\n"+ces.mkString("  |  "))

              case None =>
                solutions ::= sol
                reporter.info("Solution was not trusted but verification passed!")
            }
          } else {
            reporter.info("Found trusted solution!")
            solutions ::= sol
          }
        }

        if (synth.settings.generateDerivationTrees) {
          val dot = new DotGenerator(search.g)
          dot.writeFile("derivation"+DotGenerator.nextId()+".dot")
        }

        if (solutions.isEmpty) {
          reporter.error(ASCIIHelpers.title("Failed to repair!"))
        } else {
          reporter.info(ASCIIHelpers.title("Repair successful:"))
          for ((sol, i) <- solutions.reverse.zipWithIndex) {
            reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+":"))
            val expr = sol.toSimplifiedExpr(ctx, program)
            reporter.info(ScalaPrinter(expr));
          }
          reporter.info(ASCIIHelpers.title("In context:"))


          for ((sol, i) <- solutions.reverse.zipWithIndex) {
            reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+":"))
            val expr = sol.toSimplifiedExpr(ctx, program)
            val nfd = fd.duplicate;

            nfd.body = fd.body.map { b =>
              replace(Map(ci.source -> expr), b)
            }

            reporter.info(ScalaPrinter(nfd));
          }

        }
      }
  }

  def getSynthesizer(passingTests: List[Example], failingTests: List[Example]): (Synthesizer , ChooseInfo)= {
       
    val body = fd.body.get;


    val (newBody, replacedExpr) = focusRepair(program, fd, passingTests, failingTests)
    fd.body = Some(newBody)
    reporter.info("Original body size: "+formulaSize(body))
    reporter.info("Focused expr size : "+formulaSize(replacedExpr))

    val guide = Guide(replacedExpr)

    // Return synthesizer for this choose
    val soptions0 = SynthesisPhase.processOptions(ctx);

    val soptions = soptions0.copy(
      functionsToIgnore = soptions0.functionsToIgnore + fd,
      costModel = RepairCostModel(soptions0.costModel),
      rules = (soptions0.rules ++ Seq(
        //GuidedDecomp,
        //GuidedCloser,
        CEGLESS
        //TEGLESS
      )) diff Seq(ADTInduction, TEGIS, IntegerInequalities, IntegerEquation)
    );

    // extract chooses from nfd
    val Seq(ci) = ChooseInfo.extractFromFunction(ctx, program, fd, soptions)

    val nci = ci.copy(pc = and(ci.pc, guide))
    val p   = nci.problem

    (new Synthesizer(ctx, fd, program, p, soptions), nci)
  }

  private def focusRepair(program: Program, fd: FunDef, passingTests: List[Example], failingTests: List[Example]): (Expr, Expr) = {

    reporter.ifDebug { printer =>
      printer(new ExamplesTable("Tests failing:", failingTests).toString)
      printer(new ExamplesTable("Tests passing:", passingTests).toString)
    }

    val pre = fd.precondition.getOrElse(BooleanLiteral(true))
    val args = fd.params.map(_.id)
    val argsWrapped = tupleWrap(args.map(_.toVariable))

    val out = fd.postcondition.map(_._1).getOrElse(FreshIdentifier("res", true).setType(fd.returnType))

    val spec = fd.postcondition.map(_._2).getOrElse(BooleanLiteral(true))

    val body = fd.body.get

    val choose = Choose(List(out), spec)

    val evaluator = new DefaultEvaluator(ctx, program)

    // We exclude redundant failing tests, and only select the minimal tests
    val minimalFailingTests = {
            
      type FI = (FunDef, Seq[Expr])
      
      // We don't want tests whose invocation will call other failing tests.
      // This is because they will appear erroneous, 
      // even though the error comes from the called test
      val testEval = new RepairTrackingEvaluator(ctx, program)

      val failingTs = for (test <- failingTests) yield InExample(test.ins)

      failingTs foreach { ts => 
        testEval.eval(functionInvocation(fd, ts.ins))
      }
      
      val test2Tests : Map[FI, Set[FI]] = testEval.fullCallGraph

      def isFailing(fi : FI) = !testEval.fiStatus(fi) && (fi._1 == fd)
      val failing = test2Tests filter { case (from, to) => 
        isFailing(from) && (to forall (!isFailing(_)) )
      }

      failing.keySet map { case (_, args) => InExample(args) }
    }

    reporter.ifDebug { printer =>
      printer(new ExamplesTable("Minimal failing:", minimalFailingTests.toSeq).toString)
    }

    // Check how an expression behaves on tests
    //  - returns Some(true) if for all tests e evaluates to true
    //  - returns Some(false) if for all tests e evaluates to false
    //  - returns None otherwise
    def forAllTests(e: Expr, env: Map[Identifier, Expr]): Option[Boolean] = {
      val results = minimalFailingTests.map { ex =>
        val ins = ex.ins
        evaluator.eval(e, env ++ (args zip ins)) match {
          case EvaluationResults.Successful(BooleanLiteral(true))  => Some(true)
          case EvaluationResults.Successful(BooleanLiteral(false)) => Some(false)
          case e => None
        }
      }

      if (results.size == 1) {
        results.head
      } else {
        None
      }
    }

    def focus(expr: Expr, env: Map[Identifier, Expr]): (Expr, Expr) = expr match {
      case me @ MatchExpr(scrut, cases) =>
        var res: Option[(Expr, Expr)] = None

        // in case scrut is an non-variable expr, we simplify to a variable + inject in env
        for (c <- cases if res.isEmpty) {
          val cond = and(conditionForPattern(scrut, c.pattern, includeBinders = false),
                         c.optGuard.getOrElse(BooleanLiteral(true)))
          val map  = mapForPattern(scrut, c.pattern)


          forAllTests(cond, env ++ map) match {
            case Some(true) =>
              val (b, r) = focus(c.rhs, env ++ map)
              res = Some((MatchExpr(scrut, cases.map { c2 =>
                if (c2 eq c) {
                  c2.copy(rhs = b)
                } else {
                  c2
                }
              }), r))

            case Some(false) =>
              // continue until next case
            case None =>
              res = Some((choose, expr))
          }
        }

        res.getOrElse((choose, expr))
        
      case Let(id, value, body) =>
        val (b, r) = focus(body, env + (id -> value))
        (Let(id, value, b), r)

      case IfExpr(c, thn, els) =>
        forAllTests(c, env) match {
          case Some(true) =>
            val (b, r) = focus(thn, env)
            (IfExpr(c, b, els), r)
          case Some(false) =>
            val (b, r) = focus(els, env)
            (IfExpr(c, thn, b), r)
          case None =>
            (choose, expr)
        }

      case _ =>
        (choose, expr)
    }

    focus(body, Map())
  }

  def getVerificationCounterExamples(fd: FunDef, prog: Program): Option[Seq[InExample]] = {
    val timeoutMs = verifTimeoutMs.getOrElse(3000L)
    val solver = new TimeoutSolverFactory(SolverFactory.getFromSettings(ctx, prog), timeoutMs)
    val vctx = VerificationContext(ctx, prog, solver, reporter)
    val vcs = AnalysisPhase.generateVerificationConditions(vctx, Some(List(fd.id.name)))

    AnalysisPhase.checkVerificationConditions(
      vctx, 
      vcs, 
      checkInParallel = true,
      interruptOn = _.counterExample.isDefined 
    )

    var invalid = false;
    var ces = List[Seq[Expr]]()

    for (vc <- vcs.getOrElse(fd, List())) {
      if (vc.value == Some(false)) {
        invalid = true;

        vc.counterExample match {
          case Some(m) =>
            ces = fd.params.map(vd => m(vd.id)) :: ces;

          case _ =>
        }
      }
    }
    if (invalid) {
      Some(ces.map(InExample(_)))
    } else {
      None
    }
  }


  def discoverTests: (List[Example], List[Example]) = {

    import bonsai._
    import bonsai.enumerators._
    import utils.ExpressionGrammars.ValueGrammar
    import purescala.Extractors.UnwrapTuple

    val maxEnumerated = 1000
    val maxValid      = 400

    val evaluator = new CodeGenEvaluator(ctx, program, CodeGenParams(checkContracts = true))
    val enum      = new MemoizedEnumerator[TypeTree, Expr](ValueGrammar.getProductions _)

    val inputs = enum.iterator(tupleTypeWrap(fd.params map { _.getType})).map{ case UnwrapTuple(is) => is }

    val filtering: Seq[Expr] => Boolean = fd.precondition match {
      case None =>
        _ => true
      case Some(pre) =>
        evaluator.compile(pre, fd.params map { _.id }) match {
          case Some(evalFun) =>
            val sat = EvaluationResults.Successful(BooleanLiteral(true));
            { (e: Seq[Expr]) => evalFun(e) == sat }
          case None =>
            { _ => false }
        }
    }

    val inputsToExample: Seq[Expr] => Example = { ins =>
      evaluator.eval(FunctionInvocation(fd.typed(fd.tparams.map(_.tp)), ins)) match {
        case EvaluationResults.Successful(res) =>
          new InOutExample(ins, List(res))
        case _ =>
          new InExample(ins)
      }
    }
    
    val generatedTests = inputs
      .take(maxEnumerated)
      .filter(filtering)
      .take(maxValid)
      .map(inputsToExample)
      .toList

    val (generatedPassing, generatedFailing) = generatedTests.partition {
      case _: InOutExample => true
      case _               => false
    }

    // Extract passing/failing from the passes in POST
    val ef = new ExamplesFinder(ctx, program)
    val (userPassing, userFailing) = ef.extractTests(fd)   
    
    // If we have no ce yet, try to verify, if it fails, we have at least one CE
    val ces = (generatedFailing ++ userFailing) match {
      case Seq() => getVerificationCounterExamples(fd, program) getOrElse Nil
      case nonEmpty => nonEmpty
    }

    (generatedPassing ++ userPassing, ces.toList )
  }


  // ununsed for now, but implementation could be useful later
  private def disambiguate(p: Problem, sol1: Solution, sol2: Solution): Option[(InOutExample, InOutExample)] = {
    val s1 = sol1.toSimplifiedExpr(ctx, program)
    val s2 = sol2.toSimplifiedExpr(ctx, program)

    val e = new DefaultEvaluator(ctx, program)

    def unwrap(e: Expr) = if (p.xs.size > 1) {
      val Tuple(es) = e
      es
    } else {
      Seq(e)
    }

    if (s1 == s2) {
      None
    } else {
      val diff = and(p.pc, not(Equals(s1, s2)))
      val solver = (new FairZ3Solver(ctx, program) with TimeoutSolver).setTimeout(1000)

      solver.assertCnstr(diff)
      solver.check match {
        case Some(true) =>
          val m = solver.getModel
          val inputs = p.as.map(id => m.getOrElse(id, simplestValue(id.getType)))
          val inputsMap = (p.as zip inputs).toMap

          (e.eval(s1, inputsMap), e.eval(s2, inputsMap)) match {
            case (EvaluationResults.Successful(r1), EvaluationResults.Successful(r2)) =>
              Some((InOutExample(inputs, unwrap(r1)), InOutExample(inputs, unwrap(r2))))
            case _ =>
              None
          }
        case Some(false) =>
          None
        case _ =>
          // considered as equivalent
          None
      }
    }
  }
}
