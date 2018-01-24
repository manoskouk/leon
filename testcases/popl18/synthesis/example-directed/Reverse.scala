import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Unzip {

  @production def ruleAppend[A](l1: List[A], l2: List[A]) = l1 ++ l2

  def reserve[A](l: List[A]): List[A] = {
    ???[List[A]]
  } ensuring { res =>
    (l, res) passes {
      case Nil() => Nil()
      case Cons(a, Nil()) => Cons(a, Nil())
      case Cons(a, Cons(b, Nil()))  => Cons(b, Cons(a, Nil()))
      case Cons(a, Cons(b, Cons(c, Nil()))) => Cons(c, Cons(b, Cons(a, Nil())))
    }
  }
}
