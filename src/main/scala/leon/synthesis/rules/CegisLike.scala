/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils.StreamUtils
import solvers._
import solvers.z3._

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.DefOps._
import purescala.TypeTreeOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ScalaPrinter
import utils.Helpers._

import scala.collection.mutable.{HashMap=>MutableMap, ArrayBuffer}

import evaluators._
import datagen._
import codegen.CodeGenParams

import utils._


abstract class CEGISLike[T <% Typed](name: String) extends Rule(name) {

  case class CegisParams(
    grammar: ExpressionGrammar[T],
    rootLabel: TypeTree => T,
    maxUnfoldings: Int = 3
  );

  def getParams(sctx: SynthesisContext, p: Problem): CegisParams

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    // CEGIS Flags to actiave or de-activate features
    val useUninterpretedProbe = sctx.settings.cegisUseUninterpretedProbe
    val useUnsatCores         = sctx.settings.cegisUseUnsatCores
    val useOptTimeout         = sctx.settings.cegisUseOptTimeout
    val useVanuatoo           = sctx.settings.cegisUseVanuatoo
    val useCETests            = sctx.settings.cegisUseCETests
    val useCEPruning          = sctx.settings.cegisUseCEPruning

    // Limits the number of programs CEGIS will specifically test for instead of reasonning symbolically
    val testUpTo              = 5
    val useBssFiltering       = sctx.settings.cegisUseBssFiltering
    val filterThreshold       = 1.0/2
    val evalParams            = CodeGenParams(maxFunctionInvocations = 2000)
    lazy val evaluator        = new CodeGenEvaluator(sctx.context, sctx.program, evalParams)

    val interruptManager      = sctx.context.interruptManager

    val params = getParams(sctx, p)

    if (params.maxUnfoldings == 0) {
      return Nil
    }

    class NonDeterministicProgram(val p: Problem,
                                  val initGuard: Identifier) {

      val grammar = params.grammar

      // b -> (c, ex) means the clause b => c == ex
      var mappings: Map[Identifier, (Identifier, Expr)] = Map()

      // b -> Set(c1, c2) means c1 and c2 are uninterpreted behind b, requires b to be closed
      private var guardedTerms: Map[Identifier, Set[Identifier]] = Map(initGuard -> p.xs.toSet)

      private var labels: Map[Identifier, T] = Map() ++ p.xs.map(x => x -> params.rootLabel(x.getType))

      def isBClosed(b: Identifier) = guardedTerms.contains(b)

      /**
       * Stores which b's guard which c's, which then are represented by which
       * b's:
       *
       * b -> Map(c1 -> Set(b2, b3),
       *          c2 -> Set(b4, b5))
       *
       * means b protects c1 (with sub alternatives b2/b3), and c2 (with sub b4/b5)
       */
      private var bTree = Map[Identifier, Map[Identifier, Set[Identifier]]]( initGuard -> p.xs.map(_ -> Set[Identifier]()).toMap)

      /**
       * Computes dependencies of c's
       *
       * Assuming encoding:
       * b1 => c == F(c2, c3)
       * b2 => c == F(c4, c5)
       *
       * will be represented here as c -> Set(c2, c3, c4, c5)
       */
      private var cChildren: Map[Identifier, Set[Identifier]] = Map().withDefaultValue(Set())

      // Returns all possible assignments to Bs in order to enumerate all possible programs
      def allPrograms(): Traversable[Set[Identifier]] = {
        def allChildPaths(b: Identifier): Stream[Set[Identifier]] = {
          if (isBClosed(b)) {
            Stream.empty
          } else {
            bTree.get(b) match {
              case Some(cToBs) =>
                val streams = cToBs.values.toSeq.map { children =>
                  children.toStream.flatMap(c => allChildPaths(c).map(l => l + b))
                }

                StreamUtils.cartesianProduct(streams).map { ls =>
                  ls.foldLeft(Set[Identifier]())(_ ++ _)
                }
              case None =>
                Stream.cons(Set(b), Stream.empty)
            }
          }
        }

        allChildPaths(initGuard).toSet
      }

      /*
       * Compilation/Execution of programs
       */

      type EvaluationResult = EvaluationResults.Result

      private var triedCompilation = false
      private var progEvaluator: Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = None

      def canTest(): Boolean = {
        if (!triedCompilation) {
          progEvaluator = compile()
        }

        progEvaluator.isDefined
      }

      private var bssOrdered: Seq[Identifier] = Seq()

      def testForProgram(bss: Set[Identifier])(ins: Seq[Expr]): Boolean = {
        if (canTest()) {
          val bssValues : Seq[Expr] = bssOrdered.map(i => BooleanLiteral(bss(i)))

          val evalResult = progEvaluator.get.apply(bssValues,  ins)

          evalResult match {
            case EvaluationResults.Successful(res) =>
              res == BooleanLiteral(true)

            case EvaluationResults.RuntimeError(err) =>
              false

            case EvaluationResults.EvaluatorError(err) =>
              sctx.reporter.error("Error testing CE: "+err)
              false
          }
        } else {
          true
        }
      }

      def compile(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
        var unreachableCs: Set[Identifier] = guardedTerms.flatMap(_._2).toSet

        val cToExprs = mappings.groupBy(_._2._1).map {
          case (c, maps) =>
            // We only keep cases within the current unfoldings closedBs
            val cases = maps.flatMap{ case (b, (_, ex)) => if (isBClosed(b)) None else Some(b -> ex) }

            // We compute the IF expression corresponding to each c
            val ifExpr = if (cases.isEmpty) {
              // This can happen with ADTs with only cases with arguments
              Error(c.getType, "No valid clause available")
            } else {
              cases.tail.foldLeft(cases.head._2) {
                case (elze, (b, thenn)) => IfExpr(Variable(b), thenn, elze)
              }
            }

            c -> ifExpr
        }.toMap

        // Map each x generated by the program to fresh xs passed as argument
        val newXs = p.xs.map(x => x -> FreshIdentifier(x.name, true).setType(x.getType))

        val baseExpr = p.phi

        bssOrdered = bss.toSeq.sortBy(_.id)

        var res = baseExpr

        def composeWith(c: Identifier) {
          cToExprs.get(c) match {
            case Some(value) =>
              res = Let(c, cToExprs(c), res)
            case None =>
              res = Let(c, Error(c.getType, "No value available"), res)
          }

          for (dep <- cChildren(c) if !unreachableCs(dep)) {
            composeWith(dep)
          }

        }

        for (c <- p.xs) {
          composeWith(c)
        }

        val simplerRes = simplifyLets(res)

        def compileWithArray(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
          val ba = FreshIdentifier("bssArray").setType(ArrayType(BooleanType))
          val bav = Variable(ba)
          val substMap : Map[Expr,Expr] = (bssOrdered.zipWithIndex.map {
            case (b,i) => Variable(b) -> ArraySelect(bav, IntLiteral(i))
          }).toMap
          val forArray = replace(substMap, simplerRes)

          // We trust arrays to be fast...
          val eval = evaluator.compile(forArray, ba +: p.as)

          eval.map{e => { case (bss, ins) => 
            e(FiniteArray(bss).setType(ArrayType(BooleanType)) +: ins)
          }}
        }

        def compileWithArgs(): Option[(Seq[Expr], Seq[Expr]) => EvaluationResult] = {
          val eval = evaluator.compile(simplerRes, bssOrdered ++ p.as)

          eval.map{e => { case (bss, ins) => 
            e(bss ++ ins)
          }}
        }

        triedCompilation = true

        val localVariables = bss.size + cToExprs.size + p.as.size

        if (localVariables < 128) {
          compileWithArgs().orElse(compileWithArray())
        } else {
          compileWithArray()
        }
      }

      def determinize(bss: Set[Identifier]): Expr = {
        val cClauses = mappings.filterKeys(bss).map(_._2).toMap

        def getCValue(c: Identifier): Expr = {
          val map = for (dep <- cChildren(c) if cClauses contains dep) yield {
            dep -> getCValue(dep)
          }

          substAll(map.toMap, cClauses(c))
        }

        Tuple(p.xs.map(c => getCValue(c)))

      }

      /**
       * Shrinks the non-deterministic program to the provided set of
       * alternatives only
       */
      def filterFor(remainingBss: Set[Identifier]): Seq[Expr] = {
        val filteredBss = remainingBss + initGuard

        // The following code is black-magic, read with caution
        mappings     = mappings.filterKeys(filteredBss)
        guardedTerms = Map()
        bTree        = bTree.filterKeys(filteredBss)
        bTree        = bTree.mapValues(cToBs => cToBs.mapValues(bs => bs & filteredBss))

        val filteredCss  = mappings.map(_._2._1).toSet
        cChildren        = cChildren.filterKeys(filteredCss)
        cChildren        = cChildren.mapValues(css => css & filteredCss)
        for (c <- filteredCss) {
          if (!(cChildren contains c)) {
            cChildren += c -> Set()
          }
        }

        // Finally, we reset the state of the evaluator
        triedCompilation = false
        progEvaluator    = None


        var cGroups = Map[Identifier, (Set[Identifier], Set[Identifier])]()

        for ((parentGuard, cToBs) <- bTree; (c, bss) <- cToBs) {
          val (ps, bs) = cGroups.getOrElse(c, (Set[Identifier](), Set[Identifier]()))

          cGroups += c -> (ps + parentGuard, bs ++ bss)
        }

        // We need to regenerate clauses for each b
        val pathConstraints = for ((_, (parentGuards, bs)) <- cGroups) yield {
          val bvs = bs.toList.map(Variable(_))

          // Represents the case where all parents guards are false, indicating
          // that this C should not be considered at all
          val failedPath = andJoin(parentGuards.toSeq.map(p => Not(p.toVariable)))

          val distinct = bvs.combinations(2).collect {
            case List(a, b) =>
              or(not(a), not(b))
          }

          andJoin(Seq(orJoin(failedPath :: bvs), implies(failedPath, andJoin(bvs.map(Not(_))))) ++ distinct)
        }

        // Generate all the b => c = ...
        val impliess = mappings.map { case (bid, (recId, ex)) =>
          implies(Variable(bid), Equals(Variable(recId), ex))
        }

        (pathConstraints ++ impliess).toSeq
      }

      def unfold(finalUnfolding: Boolean): (List[Expr], Set[Identifier]) = {
        var newClauses      = List[Expr]()
        var newGuardedTerms = Map[Identifier, Set[Identifier]]()
        var newMappings     = Map[Identifier, (Identifier, Expr)]()


        var cGroups = Map[Identifier, Set[Identifier]]()

        for ((parentGuard, recIds) <- guardedTerms; recId <- recIds) {
          cGroups += recId -> (cGroups.getOrElse(recId, Set()) + parentGuard)
        }

        for ((recId, parentGuards) <- cGroups) {

          var alts = grammar.getProductions(labels(recId))
          if (finalUnfolding) {
            alts = alts.filter(_.subTrees.isEmpty)
          }

          val altsWithBranches = alts.map(alt => FreshIdentifier("B", true).setType(BooleanType) -> alt)

          val bvs  = altsWithBranches.map(alt => Variable(alt._1))

          // Represents the case where all parents guards are false, indicating
          // that this C should not be considered at all
          val failedPath = andJoin(parentGuards.toSeq.map(p => not(p.toVariable)))

          val distinct = bvs.combinations(2).collect {
            case List(a, b) =>
              or(not(a), not(b))
          }

          val pre = andJoin(Seq(orJoin(failedPath +: bvs), implies(failedPath, andJoin(bvs.map(Not(_))))) ++ distinct)

          var cBankCache = Map[T, Stream[Identifier]]()
          def freshC(t: T): Stream[Identifier] = Stream.cons(FreshIdentifier("c", true).setType(t.getType), freshC(t))
          def getC(t: T, index: Int) = cBankCache.getOrElse(t, {
            cBankCache += t -> freshC(t)
            cBankCache(t)
          })(index)

          val cases = for((bid, gen) <- altsWithBranches.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            val newLabels = for ((t, i) <- gen.subTrees.zipWithIndex) yield { getC(t, i) -> t }
            labels ++= newLabels

            val rec = newLabels.map(_._1)
            val ex = gen.builder(rec.map(_.toVariable))

            if (!rec.isEmpty) {
              newGuardedTerms += bid -> rec.toSet
              cChildren       += recId -> (cChildren(recId) ++ rec)
            }

            newMappings  += bid -> (recId -> ex)

            implies(Variable(bid), Equals(Variable(recId), ex))
          }

          val newBIds = altsWithBranches.map(_._1).toSet

          for (parentGuard <- parentGuards) {
            bTree += parentGuard -> (bTree.getOrElse(parentGuard, Map()) + (recId -> newBIds))
          }

          newClauses = newClauses ::: pre :: cases
        }

        sctx.reporter.ifDebug { printer =>
          printer("Grammar so far:");
          grammar.printProductions(printer)
        }

        //program  = And(program :: newClauses)

        mappings = mappings ++ newMappings

        guardedTerms = newGuardedTerms

        // Finally, we reset the state of the evaluator
        triedCompilation = false
        progEvaluator    = None

        (newClauses, newGuardedTerms.keySet)
      }

      def bss = mappings.keySet
      def css : Set[Identifier] = mappings.values.map(_._1).toSet ++ guardedTerms.flatMap(_._2)
    }

    List(new RuleInstantiation(p, this, SolutionBuilder.none, this.name, this.priority) {
      def apply(sctx: SynthesisContext): RuleApplication = {
        var result: Option[RuleApplication]   = None

        var ass = p.as.toSet
        var xss = p.xs.toSet

        val initGuard = FreshIdentifier("START", true).setType(BooleanType)

        val ndProgram = new NonDeterministicProgram(p, initGuard)
        var unfolding = 1
        val maxUnfoldings = params.maxUnfoldings

        sctx.reporter.debug(s"maxUnfoldings=$maxUnfoldings")

        val exSolverTo  = 2000L
        val cexSolverTo = 2000L

        var baseExampleInputs: ArrayBuffer[Seq[Expr]] = new ArrayBuffer[Seq[Expr]]()

        // We populate the list of examples with a predefined one
        sctx.reporter.debug("Acquiring list of examples")

        val ef = new ExamplesFinder(sctx.context, sctx.program)
        baseExampleInputs ++= ef.extractTests(p).map(_.ins).toSet

        val pc = p.pc

        if (pc == BooleanLiteral(true)) {
          baseExampleInputs += p.as.map(a => simplestValue(a.getType))
        } else {
          val solver = sctx.newSolver.setTimeout(exSolverTo)

          solver.assertCnstr(pc)

          try {
            solver.check match {
              case Some(true) =>
                val model = solver.getModel
                baseExampleInputs += p.as.map(a => model.getOrElse(a, simplestValue(a.getType)))

              case Some(false) =>
                sctx.reporter.debug("Path-condition seems UNSAT")
                return RuleFailed()

              case None =>
                sctx.reporter.warning("Solver could not solve path-condition")
                return RuleFailed() // This is not necessary though, but probably wanted
            }
          } finally {
            solver.free()
          }
        }

        sctx.reporter.ifDebug { debug =>
          baseExampleInputs.foreach { in =>
            debug("  - "+in.mkString(", "))
          }
        }

        /**
         * We generate tests for discarding potential programs
         */
        val inputIterator: Iterator[Seq[Expr]] = if (useVanuatoo) {
          new VanuatooDataGen(sctx.context, sctx.program).generateFor(p.as, pc, 20, 3000)
        } else {
          new NaiveDataGen(sctx.context, sctx.program, evaluator).generateFor(p.as, pc, 20, 1000)
        }

        val cachedInputIterator = new Iterator[Seq[Expr]] {
          def next() = {
            val i = inputIterator.next()
            baseExampleInputs += i
            i
          }

          def hasNext() = inputIterator.hasNext
        }

        val failedTestsStats = new MutableMap[Seq[Expr], Int]().withDefaultValue(0)

        def hasInputExamples() = baseExampleInputs.size > 0 || cachedInputIterator.hasNext

        var n = 1;
        def allInputExamples() = {
          if (n % 1000 == 0) {
            baseExampleInputs = baseExampleInputs.sortBy(e => -failedTestsStats(e))
          }
          n += 1
          baseExampleInputs.iterator ++ cachedInputIterator
        }

        def checkForPrograms(programs: Set[Set[Identifier]]): RuleApplication = {
          for (prog <- programs) {
            val expr = ndProgram.determinize(prog)
            val res = Equals(Tuple(p.xs.map(Variable(_))), expr)

            val solver3 = sctx.newSolver.setTimeout(cexSolverTo)
            solver3.assertCnstr(and(pc, res, not(p.phi)))

            try {
              solver3.check match {
                case Some(false) =>
                  return RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = true))
                case None =>
                  return RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false))
                case Some(true) =>
                  // invalid program, we skip
              }
            } finally {
              solver3.free()
            }
          }

          RuleFailed()
        }

        // Keep track of collected cores to filter programs to test
        var collectedCores = Set[Set[Identifier]]()

        val initExClause  = and(pc, p.phi,      Variable(initGuard))
        val initCExClause = and(pc, not(p.phi), Variable(initGuard))

        // solver1 is used for the initial SAT queries
        var solver1 = sctx.newSolver.setTimeout(exSolverTo)
        solver1.assertCnstr(initExClause)

        // solver2 is used for validating a candidate program, or finding new inputs
        var solver2 = sctx.newSolver.setTimeout(cexSolverTo)
        solver2.assertCnstr(initCExClause)

        var didFilterAlready = false

        val tpe = TupleType(p.xs.map(_.getType))

        try {
          do {
            var skipCESearch = false

            var bssAssumptions = Set[Identifier]()

            if (!didFilterAlready) {
              val (clauses, closedBs) = ndProgram.unfold(unfolding == maxUnfoldings)

              bssAssumptions = closedBs

              sctx.reporter.ifDebug { debug =>
                debug("UNFOLDING: ")
                for (c <- clauses) {
                  debug(" - " + c.asString(sctx.context))
                }
                debug("CLOSED Bs "+closedBs)
              }

              val clause = andJoin(clauses)

              solver1.assertCnstr(clause)
              solver2.assertCnstr(clause)

              if (clauses.isEmpty) {
                unfolding = maxUnfoldings
              }
            }

            // Compute all programs that have not been excluded yet
            var prunedPrograms: Set[Set[Identifier]] = if (useCEPruning) {
                ndProgram.allPrograms.filterNot(p => collectedCores.exists(c => c.subsetOf(p))).toSet
              } else {
                Set()
              }

            val allPrograms = prunedPrograms.size

            sctx.reporter.debug("#Programs: "+prunedPrograms.size)

            var wrongPrograms = Set[Set[Identifier]]();

            // We further filter the set of working programs to remove those that fail on known examples
            if (useCEPruning && hasInputExamples() && ndProgram.canTest()) {

              for (bs <- prunedPrograms if !interruptManager.isInterrupted()) {
                var valid = true
                val examples = allInputExamples()
                while(valid && examples.hasNext) {
                  val e = examples.next()
                  if (!ndProgram.testForProgram(bs)(e)) {
                    failedTestsStats(e) += 1
                    //sctx.reporter.debug(" Program: "+ndProgram.determinize(bs)+" failed on "+e)
                    wrongPrograms += bs
                    prunedPrograms -= bs

                    valid = false;
                  }
                }

                if (wrongPrograms.size % 1000 == 0) {
                  sctx.reporter.debug("..."+wrongPrograms.size)
                }
              }
            }

            val nPassing = prunedPrograms.size
            sctx.reporter.debug("#Programs passing tests: "+nPassing)

            if (nPassing == 0 || interruptManager.isInterrupted()) {
              skipCESearch = true;
            } else if (nPassing <= testUpTo) {
              // Immediate Test
              checkForPrograms(prunedPrograms) match {
                case rs: RuleClosed if rs.solutions.nonEmpty =>
                  result = Some(rs)
                case _ =>
                  wrongPrograms.foreach { p =>
                    solver1.assertCnstr(Not(andJoin(p.map(Variable(_)).toSeq)))
                  }
              }
            } else if (((nPassing < allPrograms*filterThreshold) || didFilterAlready) && useBssFiltering) {
              // We filter the Bss so that the formula we give to z3 is much smalled
              val bssToKeep = prunedPrograms.foldLeft(Set[Identifier]())(_ ++ _)

              // Cannot unfold normally after having filtered, so we need to
              // repeat the filtering procedure at next unfolding.
              didFilterAlready = true
              
              // Freshening solvers
              solver1.free()
              solver1 = sctx.newSolver.setTimeout(exSolverTo)
              solver1.assertCnstr(initExClause)

              solver2.free()
              solver2 = sctx.newSolver.setTimeout(cexSolverTo)
              solver2.assertCnstr(initCExClause)

              val clauses = ndProgram.filterFor(bssToKeep)
              val clause  = andJoin(clauses)

              solver1.assertCnstr(clause)
              solver2.assertCnstr(clause)
            } else {
              wrongPrograms.foreach { p =>
                solver1.assertCnstr(not(andJoin(p.map(_.toVariable).toSeq)))
              }
            }

            val bss = ndProgram.bss

            while (result.isEmpty && !skipCESearch && !interruptManager.isInterrupted()) {

              solver1.checkAssumptions(bssAssumptions.map(id => Not(Variable(id)))) match {
                case Some(true) =>
                  val satModel = solver1.getModel

                  val bssAssumptions: Set[Expr] = bss.map(b => satModel(b) match {
                    case BooleanLiteral(true)  => Variable(b)
                    case BooleanLiteral(false) => Not(Variable(b))
                  })

                  val validateWithZ3 = if (useCETests && hasInputExamples() && ndProgram.canTest()) {

                    val p = bssAssumptions.collect { case Variable(b) => b }

                    if (allInputExamples().forall(ndProgram.testForProgram(p))) {
                      // All valid inputs also work with this, we need to
                      // make sure by validating this candidate with z3
                      true
                    } else {
                      // One valid input failed with this candidate, we can skip
                      solver1.assertCnstr(not(andJoin(p.map(_.toVariable).toSeq)))
                      false
                    }
                  } else {
                    // No inputs or capability to test, we need to ask Z3
                    true
                  }

                  if (validateWithZ3) {
                    solver2.checkAssumptions(bssAssumptions) match {
                      case Some(true) =>
                        val invalidModel = solver2.getModel

                        val fixedAss = andJoin(ass.collect {
                          case a if invalidModel contains a => Equals(Variable(a), invalidModel(a))
                        }.toSeq)

                        val newCE = p.as.map(valuateWithModel(invalidModel))

                        baseExampleInputs += newCE

                        // Retest whether the newly found C-E invalidates all programs
                        if (useCEPruning && ndProgram.canTest) {
                          if (prunedPrograms.forall(p => !ndProgram.testForProgram(p)(newCE))) {
                            skipCESearch = true
                          }
                        }

                        val unsatCore = if (useUnsatCores) {
                          solver1.push()
                          solver1.assertCnstr(fixedAss)

                          val core = solver1.checkAssumptions(bssAssumptions) match {
                            case Some(false) =>
                              // Core might be empty if unfolding level is
                              // insufficient, it becomes unsat no matter what
                              // the assumptions are.
                              solver1.getUnsatCore

                            case Some(true) =>
                              // Can't be!
                              bssAssumptions

                            case None =>
                              return RuleFailed()
                          }

                          solver1.pop()

                          collectedCores += core.collect{ case Variable(id) => id }

                          core
                        } else {
                          bssAssumptions
                        }

                        if (unsatCore.isEmpty) {
                          skipCESearch = true
                        } else {
                          solver1.assertCnstr(not(andJoin(unsatCore.toSeq)))
                        }

                      case Some(false) =>

                        val expr = ndProgram.determinize(satModel.filter(_._2 == BooleanLiteral(true)).keySet)

                        result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr)))

                      case _ =>
                        if (useOptTimeout) {
                          // Interpret timeout in CE search as "the candidate is valid"
                          sctx.reporter.info("CEGIS could not prove the validity of the resulting expression")
                          val expr = ndProgram.determinize(satModel.filter(_._2 == BooleanLiteral(true)).keySet)
                          result = Some(RuleClosed(Solution(BooleanLiteral(true), Set(), expr, isTrusted = false)))
                        } else {
                          return RuleFailed()
                        }
                    }
                  }


                case Some(false) =>
                  if (useUninterpretedProbe) {
                    solver1.check match {
                      case Some(false) =>
                        // Unsat even without blockers (under which fcalls are then uninterpreted)
                        return RuleFailed()

                      case _ =>
                    }
                  }

                  skipCESearch = true

                case _ =>
                  // Last chance, we test first few programs
                  result = Some(checkForPrograms(prunedPrograms.take(testUpTo)))
              }
            }

            unfolding += 1
          } while(unfolding <= maxUnfoldings && result.isEmpty && !interruptManager.isInterrupted())

          result.getOrElse(RuleFailed())

        } catch {
          case e: Throwable =>
            sctx.reporter.warning("CEGIS crashed: "+e.getMessage)
            e.printStackTrace
            RuleFailed()
        } finally {
          solver1.free()
          solver2.free()
        }
      }
    })
  }
}
