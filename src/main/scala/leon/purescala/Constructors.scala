/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

object Constructors {
  import Trees._
  import Common._
  import TypeTrees._

  def tupleSelect(t: Expr, index: Int) = t match {
    case Tuple(es) =>
      es(index-1)
    case _ =>
      TupleSelect(t, index)
  }

  def letTuple(binders: Seq[Identifier], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      Let(x, tupleSelect(value, 1), body)
    case xs =>
      LetTuple(xs, value, body)
  }

  def tupleChoose(ch: Choose): Expr = {
    if (ch.vars.size > 1) {
      ch
    } else {
      Tuple(Seq(ch))
    }
  }

  def tupleWrap(es: Seq[Expr]): Expr = if (es.size > 1) {
    Tuple(es)
  } else {
    es.head
  }

  def matchExpr(scrutinee: Expr, cases: Seq[MatchCase]): MatchExpr = {
    scrutinee.getType match {
      case c: CaseClassType =>
        new MatchExpr(scrutinee,
          cases.filter(_.pattern match {
            case CaseClassPattern(_, cct, _) if cct.classDef != c.classDef => false
            case _ => true
          })
        )

      case _: TupleType | Int32Type | BooleanType | UnitType | _: AbstractClassType =>
        new MatchExpr(scrutinee, cases)

      case t =>
        scala.sys.error("Constructing match expression on non-supported type: "+t)
    }
  }
}
