/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.evaluators

import leon.LeonContext
import leon.evaluators._
import leon.purescala.Definitions.Program
import leon.purescala.Expressions.Expr
import leon.test.LeonTestSuiteWithProgram
import leon.test.helpers.ExpressionsDSL

class StreamEvaluatorSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {
  val sources = List(
    """import leon.lang._
      |import leon.lang.synthesis._
      |
      |object Cond {
      |  sealed abstract class List {
      |    def head = {
      |      require(this.isInstanceOf[Cons])
      |      val Cons(h, _) = this
      |      h
      |    }
      |    def tail = {
      |      require(this.isInstanceOf[Cons])
      |      val Cons(_, t) = this
      |      t
      |    }
      |
      |    def ::(i: BigInt) = Cons(i, this)
      |
      |    def size:BigInt = this match {
      |      case Nil() => 0
      |      case Cons(_, t) => t.size + 1
      |    }
      |  }
      |  case class Nil() extends List
      |  case class Cons(h: BigInt, t: List) extends List
      |
      |  def isSorted(l: List): Boolean = l match {
      |    case Cons(x, Cons(y, t)) =>
      |      x <= y && isSorted(Cons(y, t))
      |    case _ =>
      |      true
      |  }
      |
      |  def insert(l: List, e: BigInt): List = {
      |    require(isSorted(l))
      |    conditionally(
      |      e :: l,
      |      l.head :: insert(l.tail, e)
      |    )
      |  } ensuring { res =>
      |    //res.content == l.content ++ Set(e) &&
      |    isSorted(res)
      |  }
      |
      |  def merge(l1 : List, l2 : List) : List = {
      |    //require(isSorted(l1) && isSorted(l2))
      |    conditionally(
      |      l1,
      |      l2,
      |      l1.head :: merge(l1.tail, l2),
      |      l2.head :: merge(l1, l2.tail)
      |    )
      |  } ensuring { res =>
      |    //isSorted(res) &&
      |    res.size == l1.size + l2.size //&&
      |    //res.content == l1.content ++ l2.content
      |  }
      |
      |}
      |""".stripMargin
  )


  def ndEvaluators(implicit ctx: LeonContext, pgm: Program): List[NDEvaluator] = {
    List(
      new StreamEvaluator(ctx, pgm)
    )
  }

  test("StreamEvaluator") { implicit fix =>
    val nil = cc("Cond.Nil")()
    def list(es: Expr*) = es.foldRight(nil)(cc("Cond.Cons")(_, _))
    def ins(es: Expr*) = fcall("Cond.insert")(es: _*)
    def merge(es: Expr*) = fcall("Cond.merge")(es: _*)

    val l1 = list(bi(1), bi(3))
    val l2 = list(bi(2), bi(4))

    for (e <- ndEvaluators) {
      e.eval(ins(l1, bi(2))) match {
        case EvaluationResults.Successful(Stream(sol)) =>
          sol === list(bi(1), bi(2), bi(3))
        case _ =>
          fail("")
      }

      e.eval(merge(l1, l2)) match {
        case EvaluationResults.Successful(s) if
            s.contains(list(bi(1), bi(2), bi(3), bi(4))) &&
            s.contains(list(bi(2), bi(1), bi(4), bi(3)))
          => // Success!
        case _ =>
          fail("")
      }
    }

  }

}