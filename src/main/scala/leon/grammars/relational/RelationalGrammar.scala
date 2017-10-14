package leon.grammars
package relational

import leon.LeonContext
import leon.purescala.Expressions.Expr
import leon.purescala.Types._
import leon.purescala.TypeOps._
import leon.purescala.Common._
import leon.purescala.Definitions.TypeParameterDef
import leon.purescala.{PrettyPrintable, PrinterContext}
import leon.purescala.PrinterHelpers._

object RelationalAlg {
  trait RelType extends TypeTree with PrettyPrintable { val arity: Int }
  //case class Const(id: Int) extends RelType {
  //  def printWith(implicit pctx: PrinterContext): Unit = {
  //    p"T$id"
  //  }
  //  val arity = 1
  //}
  //case class TupleType(subs: Seq[TypeTree]) extends RelType {
  //  val arity = subs.size
  //  require(subs.size > 1)
//
  //  def printWith(implicit pctx: PrinterContext): Unit = {
  //    p"${nary(subs, ", ", "(", ")")}"
  //  }
  //}

  def flatten(tps: Seq[TypeTree]): TypeTree = {
    require(tps.nonEmpty)
    tps match {
      case Seq(one) => one
      case more =>
        TupleType(more flatMap {
          case TupleType(subs) => subs
          case other => Seq(other)
        })
    }
  }

  trait RelExpr extends Expr with PrettyPrintable

  case class Union(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 + $e2"
    }
  }
  case class Inters(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 & $e2"
    }
  }
  case class Diff(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 - $e2"
    }
  }

  case class Cross(e1: Expr, e2: Expr) extends RelExpr {
    val getType = flatten(Seq(e1.getType, e2.getType))
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 -> $e2"
    }
  }

  case class Join(e1: Expr, e2: Expr) extends RelExpr {
    val getType = (e1.getType, e2.getType) match {
      case (TupleType(tps1), TupleType(tps2)) if tps1.last == tps2.head =>
        TupleType(tps1.init ++ tps2.tail)
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 . $e2"
    }
  }

  case class Transpose(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) => TupleType(Seq(t2, t1))
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"~$e1"
    }
  }
  case class RefTransClosure(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) if t1 == t2 => e1.getType
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"^$e1"
    }
  }

  case class TransClosure(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) if t1 == t2 => e1.getType
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"*$e1"
    }
  }

  case class Variable(id: Identifier) extends RelExpr {
    val getType = id.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$id"
    }
  }
}

import RelationalAlg._

case class RelationalGrammar(vars: Seq[Identifier]) extends ExpressionGrammar {

  def generateProductions(implicit ctx: LeonContext) = {
    val tps@List(a, b, c, d) = List("A", "B", "C", "D") map (n => TypeParameter.fresh(n))

    def binary(f: (Expr, Expr) => Expr) =
      GenericProdSeed(List(TypeParameterDef(a)), Label(a), List(a, a), map => {
        val label = Label(instantiateType(a, map))
        ProductionRule(
          List(label, label), { case Seq(e1, e2) => f(e1, e2) }, Tags.Top, 1, -1.0
        )
      })

    def unary(f: Expr => Expr) = {
      val tp = TupleType(Seq(a, a))
      GenericProdSeed(List(TypeParameterDef(a)), Label(tp), List(tp), map => {
        val label = Label(instantiateType(tp, map))
        ProductionRule(
          List(label), { case Seq(e1) => f(e1) }, Tags.Top, 1, -1.0
        )
      })
    }

    def cross(l: Int) = {
      val tparams = tps.take(l)
      for (x <- 1 until l) yield {
        val (first, last) = tparams.splitAt(x)
        val subtps = List(flatten(first), flatten(last))
        GenericProdSeed(tparams.map(TypeParameterDef), Label(flatten(tparams)), subtps, map => {
          //println(map)
          val labels = subtps map (tp => Label(instantiateType(tp, map)))

          ProductionRule(
            labels, { case Seq(e1, e2) => Cross(e1, e2) }, Tags.Top, 1, -1.0
          )
        })
      }
    }

    def trans =
      GenericProdSeed(List(TypeParameterDef(a), TypeParameterDef(b)), Label(TupleType(Seq(b, a))), List(TupleType(Seq(a, b))), map => {
        val label = Label(instantiateType(TupleType(Seq(a, b)), map))
        ProductionRule(
          List(label), { case Seq(e1) => Transpose(e1) }, Tags.Top, 1, -1.0
        )
      })

    def vr(id: Identifier) = {
      terminal(Label(id.getType), Variable(id), Tags.Top)
    }

    def join(l: Int) = {
      val input = tps.take(l)
      val joinTp = tps(l)
      for (x <- 1 until l) yield {
        val first = flatten( (input take x) :+ joinTp)
        val last  = flatten( joinTp +: (input drop x))
        val tps = (input take x) ++ Seq(joinTp) ++ (input drop x)
        GenericProdSeed(tps.map(TypeParameterDef), Label(TupleType(input)), List(first, last), map => {
          val labels = List(first, last) map (tp => Label(instantiateType(tp, map)))
          ProductionRule(
            labels, { case Seq(e1, e2) => Join(e1, e2) }, Tags.Top, 1, -1.0
          )
        })
      }
    }

    val maxArity = 3

    vars.map(vr) ++
    (2 to maxArity).flatMap(cross) ++
    (2 to maxArity).flatMap(join) ++
    List(Union, Inters, Diff).map(binary) ++
    List(RefTransClosure, TransClosure).map(unary) ++
    List(trans)

  }
}



object RelMain {
  def main(args: Array[String]): Unit = {
    val ids = List(
      FreshIdentifier("v1", IntegerType),
      FreshIdentifier("v2", BooleanType),
      FreshIdentifier("v3", TupleType(Seq(IntegerType, BooleanType)))
    )
    implicit val ctx = LeonContext.empty
    val g = RelationalGrammar(ids)
    g.getProductions(Label(TupleType(Seq(IntegerType, BooleanType))))
    g.getProductions(Label(TupleType(Seq(IntegerType, IntegerType))))
    g.getProductions(Label((IntegerType)))
    g.getProductions(Label((BooleanType)))
    //g.getProductions(Label(Const(1)))
    println(g.asString)
  }
}
