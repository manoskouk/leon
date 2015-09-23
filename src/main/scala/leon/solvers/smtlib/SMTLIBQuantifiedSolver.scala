/* Copyright 2009-2015 EPFL, Lausanne */

package leon.solvers.smtlib

import leon.purescala.Common._
import leon.purescala.Constructors._
import leon.purescala.Definitions.FunDef
import leon.purescala.ExprOps._
import leon.purescala.Expressions._
import leon.purescala.Extractors.IsTyped
import leon.purescala.Types._
import leon.utils.IncrementalBijection

import leon.verification.VC

import smtlib.parser.Terms.{Forall => SMTForall, SSymbol, Term}
import smtlib.parser.Commands.{Assert => SMTAssert, _}
import smtlib.theories.ArraysEx

trait SMTLIBQuantifiedSolver extends SMTLIBSolver {

  private var currentFunDef: Option[FunDef] = None
  protected def refersToCurrent(fd: FunDef) = {
    (currentFunDef contains fd) || (currentFunDef exists {
      program.callGraph.transitivelyCalls(fd, _)
    })
  }

  protected val allowQuantifiedAssertions: Boolean

  protected val typedFunDefExplorationLimit = 10000

  protected def withInductiveHyp(cond: Expr): Expr = {

    val inductiveHyps = for {
      fi@FunctionInvocation(tfd, args) <- functionCallsOf(cond).toSeq
    } yield {
      val formalToRealArgs = tfd.params.map{ _.id}.zip(args).toMap
      val post = tfd.postcondition map { post =>
        application(
          replaceFromIDs(formalToRealArgs, post),
          Seq(fi)
        )
      } getOrElse BooleanLiteral(true)
      val pre = tfd.precondition getOrElse BooleanLiteral(true)
      and(pre, post)
    }

    // We want to check if the negation of the vc is sat under inductive hyp.
    // So we need to see if (indHyp /\ !vc) is satisfiable
    andJoin(inductiveHyps :+ not(cond))

  }

  private def preprocess(e: Expr) = liftLets(matchToIfThenElse(liftLambdas(withInductiveHyp(e))))

  protected def liftLambdas(e: Expr) = {
    var lambdas = Seq[Expr]()

    val lambdaFree = postMap {
      case IsTyped(Lambda(args, body), ft) =>
        val id = FreshIdentifier("lambda", ft)
        lambdas +:= Forall(args, Equals(
          application(Variable(id), args map {
            _.toVariable
          }),
          body
        ))
        Some(Variable(id))
      case _ =>
        None
    }(e)

    andJoin(lambdas :+ lambdaFree)
  }

  override protected def toSMT(e: Expr)(implicit bindings: Map[Identifier, Term]): Term = e match {
    case Application(callee, args) =>
      ArraysEx.Select(toSMT(callee), toSMT(tupleWrap(args)))
    case Forall(vs, bd) =>
      quantifiedTerm(SMTForall, vs map { _.id }, bd)
    case _ =>
      super.toSMT(e)
  }

  // We need to know the function context.
  // The reason is we do not want to assume postconditions of functions referring to
  // the current function, as this may make the proof unsound
  override def assertVC(vc: VC) = {
    currentFunDef = Some(vc.fd)
    assertCnstr(preprocess(vc.condition))
  }

  // Normally, UnrollingSolver tracks the input variable, but this one
  // is invoked alone so we have to filter them here
  override def getModel: leon.solvers.Model = {
    val filter = currentFunDef.map{ _.params.map{_.id}.toSet }.getOrElse( (_:Identifier) => true )
    getModel(filter)
  }

}
