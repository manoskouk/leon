/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

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
import purescala.ScalaPrinter
import purescala.Constructors._

import scala.collection.mutable.{Map=>MutableMap, ArrayBuffer}

import evaluators._
import datagen._
import codegen.CodeGenParams

import bonsai._
import bonsai.enumerators._

case object TEGIS extends Rule("TEGIS") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    var tests = p.getTests(sctx).map(_.ins).distinct
    if (tests.nonEmpty) {
      List(new RuleInstantiation(p, this, SolutionBuilder.none, this.name, this.priority) {
        def apply(sctx: SynthesisContext): RuleApplication = {

          val evalParams            = CodeGenParams(maxFunctionInvocations = 2000, checkContracts = true)
          //val evaluator             = new CodeGenEvaluator(sctx.context, sctx.program, evalParams)
          //val evaluator             = new DefaultEvaluator(sctx.context, sctx.program)
          val evaluator             = new DualEvaluator(sctx.context, sctx.program, evalParams)

          val interruptManager      = sctx.context.interruptManager

          def getBaseGenerators(t: TypeTree): Seq[Generator[TypeTree, Expr]] = t match {
            case BooleanType =>
              List(
                Generator(Nil, { _ => BooleanLiteral(true) }),
                Generator(Nil, { _ => BooleanLiteral(false) })
              )
            case Int32Type =>
              List(
                Generator(Nil, { _ => IntLiteral(0) }),
                Generator(Nil, { _ => IntLiteral(1) }),
                Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Plus(a, b) }),
                Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Minus(a, b) }),
                Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Times(a, b) })
              )
            case TupleType(stps) =>
              List(Generator(stps, { sub => Tuple(sub) }))

            case cct: CaseClassType =>
              List(
                Generator(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
              )

            case act: AbstractClassType =>
              act.knownCCDescendents.map { cct =>
                Generator[TypeTree, Expr](cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
              }

            case st @ SetType(base) =>
              List(
                Generator(List(base),   { case elems     => FiniteSet(elems.toSet).setType(st) }),
                Generator(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
                Generator(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
                Generator(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
              )

            case _ =>
              Nil
          }

          def getInputGenerators(t: TypeTree): Seq[Generator[TypeTree, Expr]] = {
            p.as.filter(id => isSubtypeOf(id.getType, t)).map {
              a => Generator[TypeTree, Expr](Nil, { _ => Variable(a) })
            }
          }

          def getFcallGenerators(t: TypeTree): Seq[Generator[TypeTree, Expr]] = {
            def getCandidates(fd: FunDef): Seq[TypedFunDef] = {
              // Prevents recursive calls

              val cfd = sctx.functionContext

              val isRecursiveCall = (sctx.program.callGraph.transitiveCallers(cfd) + cfd) contains fd

              val isNotSynthesizable = fd.body match {
                case Some(b) =>
                  !containsChoose(b)

                case None =>
                  false
              }


              if (!isRecursiveCall && isNotSynthesizable) {
                val free = fd.tparams.map(_.tp)
                canBeSubtypeOf(fd.returnType, free, t) match {
                  case Some(tpsMap) =>
                    val tfd = fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp)))

                    if (tpsMap.size < free.size) {
                      /* Some type params remain free, we want to assign them:
                       *
                       * List[T] => Int, for instance, will be found when
                       * requesting Int, but we need to assign T to viable
                       * types. For that we use problem inputs as heuristic,
                       * and look for instantiations of T such that input <?:
                       * List[T].
                       */
                      p.as.map(_.getType).distinct.flatMap { (atpe: TypeTree) =>
                        var finalFree = free.toSet -- tpsMap.keySet
                        var finalMap = tpsMap

                        for (ptpe <- tfd.params.map(_.tpe).distinct) {
                          canBeSubtypeOf(atpe, finalFree.toSeq, ptpe) match {
                            case Some(ntpsMap) =>
                              finalFree --= ntpsMap.keySet
                              finalMap  ++= ntpsMap
                            case _ =>
                          }
                        }

                        if (finalFree.isEmpty) {
                          List(fd.typed(free.map(tp => finalMap.getOrElse(tp, tp))))
                        } else {
                          Nil
                        }
                      }
                    } else {
                      /* All type parameters that used to be free are assigned
                       */
                      List(tfd)
                    }
                  case None =>
                    Nil
                }
              } else {
                Nil
              }
            }

            val funcs = visibleFunDefsFromMain(sctx.program).toSeq.flatMap(getCandidates)

            funcs.map{ tfd =>
              Generator[TypeTree, Expr](tfd.params.map(_.tpe), { sub => FunctionInvocation(tfd, sub) })
            }
          }

          def getGenerators(t: TypeTree): Seq[Generator[TypeTree, Expr]] = {
            val res = getBaseGenerators(t) ++ getInputGenerators(t) ++ getFcallGenerators(t)
            //for (g <- res) {
            //  val inputs = g.subTrees.zipWithIndex.map{ case (t, i) => Variable(FreshIdentifier(t.toString).setType(t)) }
            //  println(f"$t%20s  :=  ${g.builder(inputs)}")
            //}
            res
          }

          val enum = new MemoizedEnumerator[TypeTree, Expr](getGenerators)

          val (targetType, isWrapped) = if (p.xs.size == 1) {
            (p.xs.head.getType, false)
          } else {
            (TupleType(p.xs.map(_.getType)), true)
          }

          val timers = sctx.context.timers.synthesis.rules.tegis;

          val allExprs = enum.iterator(targetType)

          var failStat = Map[Seq[Expr], Int]().withDefaultValue(0)

          var candidate: Option[Expr] = None
          var enumLimit = 10000;
          var n = 1;

          def findNext(): Option[Expr] = {
            candidate = None
            timers.generating.start()
            allExprs.take(enumLimit).takeWhile(e => candidate.isEmpty).foreach { e =>
              val exprToTest = if (!isWrapped) {
                Let(p.xs.head, e, p.phi)
              } else {
                letTuple(p.xs, e, p.phi)
              }

              sctx.reporter.debug("Got expression "+e)
              timers.testing.start()
              if (tests.forall{ case t =>
                  val ts = System.currentTimeMillis
                  val res = evaluator.eval(exprToTest, p.as.zip(t).toMap) match {
                    case EvaluationResults.Successful(BooleanLiteral(true)) =>
                      sctx.reporter.debug("Test "+t+" passed!")
                      true
                    case _ =>
                      sctx.reporter.debug("Test "+t+" failed on "+e)
                      failStat += t -> (failStat(t) + 1)
                      false
                  }
                  res
                }) {
                if (isWrapped) {
                  candidate = Some(e)
                } else {
                  candidate = Some(Tuple(Seq(e)))
                }
              }
              timers.testing.stop()

              if (n % 50 == 0) {
                tests = tests.sortBy(t => -failStat(t))
              }
              n += 1
            }
            timers.generating.stop()

            candidate
          }

          def toStream(): Stream[Solution] = {
            findNext() match {
              case Some(e) =>
                Stream.cons(Solution(BooleanLiteral(true), Set(), e, isTrusted = false), toStream())
              case None =>
                Stream.empty
            }
          }

          RuleClosed(toStream())
        }
      })
    } else {
      Nil
    }
  }
}
