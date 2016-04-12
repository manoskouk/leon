/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package z3

import com.microsoft.z3._

import solvers.{Model => LeonModel}
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions.{ Expr => LeonExpr, _ }
import purescala.Types._

import unrolling._
import theories._
import utils._

import scala.language.implicitConversions

class FairZ3Solver(val context: LeonContext, val program: Program)
  extends AbstractZ3Solver
     with AbstractUnrollingSolver[Expr] {

  protected val errors     = new IncrementalBijection[Unit, Boolean]()
  protected def hasError   = errors.getB(()) == Some(true)
  protected def addError() = errors += () -> true

  override val name = "Z3-f"
  override val description = "Fair Z3 Solver"

  override protected val reporter = context.reporter
  override def reset(): Unit = super[AbstractZ3Solver].reset()

  def declareVariable(id: Identifier): Expr = variables.cachedB(Variable(id)) {
    templateEncoder.encodeId(id)
  }

  def solverCheck[R](clauses: Seq[Expr])(block: Option[Boolean] => R): R = {
    solver.push()
    for (cls <- clauses) solver.add(cls)
    val res = solver.check
    val r = block(res)
    solver.pop()
    r
  }

  override def solverCheckAssumptions[R](assumptions: Seq[Expr])(block: Option[Boolean] => R): R = {
    val res = solver.check(assumptions : _*)
    block(res)
  }

  def solverGetModel: ModelWrapper = new ModelWrapper {
    val model = solver.getModel

    def modelEval(elem: Expr, tpe: TypeTree): Option[LeonExpr] =
      softFromZ3Formula(model, model.eval(elem, true), tpe)

    override def toString = model.toString
  }

  val printable = (z3: Expr) => new Printable {
    def asString(implicit ctx: LeonContext) = z3.toString
  }

  val theoryEncoder = new StringEncoder(context, program) >> new BagEncoder(context, program)

  val templateEncoder = new TemplateEncoder[Expr] {
    def encodeId(id: Identifier): Expr = {
      idToFreshZ3Id(id)
    }

    def encodeExpr(bindings: Map[Identifier, Expr])(e: LeonExpr): Expr = {
      toZ3Formula(e, bindings)
    }

    def substitute(substMap: Map[Expr, Expr]): Expr => Expr = {
      val (from, to) = substMap.unzip
      val (fromArray, toArray) = (from.toArray, to.toArray)

      (c: Expr) => c.substitute(fromArray, toArray)
    }

    def mkNot(e: Expr) = z3.mkNot(e)
    def mkOr(es: Expr*) = z3.mkOr(es.map(castDownBool) : _*)
    def mkAnd(es: Expr*) = z3.mkAnd(es.map(castDownBool) : _*)
    def mkEquals(l: Expr, r: Expr) = z3.mkEq(l, r)
    def mkImplies(l: Expr, r: Expr) = z3.mkImplies(l, r)

    def extractNot(l: Expr): Option[Expr] = l.isNot.option(l.getArgs()(0))
  }

  private val incrementals: List[IncrementalState] = List(
    errors, functions, lambdas, sorts, variables,
    constructors, selectors, testers
  )

  override def push(): Unit = {
    super.push()
    solver.push()
    incrementals.foreach(_.push())
  }

  override def pop(): Unit = {
    super.pop()
    solver.pop(1)
    incrementals.foreach(_.pop())
  }

  override def check: Option[Boolean] = {
    if (hasError) {
      None
    } else {
      super.check
    }
  }

  override def checkAssumptions(assumptions: Set[LeonExpr]): Option[Boolean] = {
    if (hasError) {
      None
    } else {
      super.checkAssumptions(assumptions)
    }
  }

  override def assertCnstr(expression: LeonExpr): Unit = {
    try {
      super.assertCnstr(expression)
    } catch {
      case _: Unsupported =>
        addError()
    }
  }

  def solverAssert(cnstr: Expr): Unit = {
    solver.add(cnstr)
  }

  def solverUnsatCore = Some(solver.getUnsatCore)

  override def foundAnswer(res: Option[Boolean], model: LeonModel = LeonModel.empty, core: Set[LeonExpr] = Set.empty) = {
    super.foundAnswer(res, model, core)

    if (!interrupted && res.isEmpty && model.isEmpty) {
      reporter.ifDebug { debug => 
        if (solver.getReasonUnknown != "canceled") {
          debug("Z3 returned unknown: " + solver.getReasonUnknown)
        }
      }
    }
  }

  override def interrupt(): Unit = {
    super[AbstractZ3Solver].interrupt()
    super[AbstractUnrollingSolver].interrupt()
  }
}
