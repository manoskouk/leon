/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._
import purescala.Extractors._
import purescala.{PrettyPrinter, PrettyPrintable, ScalaPrinter, PrinterContext}
import utils._

object Trees {
  import purescala.PrinterHelpers._

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
    sb.append("  " * lvl)
    sb
  }

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val Block(args, rest) = this
      Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""|{
          |  ${nary(exprs :+ last, "\n")}
          |}"""
    }

    def getType = last.getType
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    val getType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"$varId = $expr;"
    }
  }

  case class While(cond: Expr, body: Expr) extends Expr with BinaryExtractable with PrettyPrintable {
    val getType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((cond, body, (t1, t2) => While(t1, t2).setInvariant(this.invariant).setPos(this)))
    }

    def printWith(implicit pctx: PrinterContext) {
      invariant match {
        case Some(inv) =>
          p"""|@invariant($inv)
              |"""
        case None =>
      }

      p"""|while($cond) {
          |  $body
          |}"""
    }
  }

  case class Epsilon(pred: Expr) extends Expr with UnaryExtractable with PrettyPrintable with MutableTyped {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr).setType(this.getType).setPos(this)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"epsilon(x${getPos.line}_${getPos.col}. $pred)"
    }
  }

  case class EpsilonVariable(pos: Position) extends Expr with Terminal with PrettyPrintable with MutableTyped {

    def printWith(implicit pctx: PrinterContext) {
      p"x${pos.line}_${pos.col}"
    }
  }

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr with BinaryExtractable with PrettyPrintable {
    def getType = body.getType

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      val LetVar(binders, expr, body) = this
      Some((expr, body, (e: Expr, b: Expr) => LetVar(binders, e, b)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""|locally {
          |  var $binder = $value
          |  $body
          |}"""
    }
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable with MutableTyped {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"waypoint_$i($expr)"
    }
  }

  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    val getType = UnitType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val ArrayUpdate(t1, t2, t3) = this
      Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"$array($index) = $newValue"
    }
  }

}
