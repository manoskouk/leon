import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.collection._
import leon.lang.synthesis._

object Diffs {

  def diffs(l: List[BigInt]): List[BigInt] = {
    ???[List[BigInt]]
    /*
    l match {
      case Nil() =>
        List[BigInt]()
      case Cons(h, t) =>
        diffs(t) match {
          case Nil() =>
            Cons[BigInt](h, t)
          case Cons(h$1, t$1) =>
            Cons[BigInt](h, Cons[BigInt](h$1 - h, t$1))
        }
    }
    */
  } ensuring { (res: List[BigInt]) =>
    (l, res) passes {
      case Nil() => Nil()
      case Cons(a, Nil()) => List(a)
      case Cons(a, Cons(b, Nil())) => List(a-b, b)
      case Cons(a, Cons(b, Cons(c, Nil()))) => List(a-b, b-c, c)
    }
  }

} 

