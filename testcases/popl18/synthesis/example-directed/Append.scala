import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Insert {
  def append[A](l1: List[A], l2: List[A]) : List[A] = {
    ???[List[A]]
  } ensuring { (res: List[A]) =>
    ((l1, l2), res) passes {
      case (Nil(), l) => l
      case (l, Nil()) => l
      case (Cons(a, Nil()), Cons(b, Nil())) => Cons(a, Cons(b, Nil()))
      case (Cons(a, Cons(b, Nil())), Cons(c, Nil())) => Cons(a, Cons(b, Cons(c, Nil())))
      case (Cons(a, Cons(b, Nil())), Cons(c, Cons(d, Nil()))) => Cons(a, Cons(b, Cons(c, Cons(d, Nil()))))
    }
  }
}
