import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Unzip {
  def unzip[A, B](l: List[(A, B)]): (List[A], List[B]) = {
    ???[(List[A], List[B])]
  } ensuring { res =>
    (l, res) passes {
      case Nil() => (Nil(), Nil())
      case Cons((a, b), Nil()) => (Cons(a, Nil()), Cons(b, Nil()))
      case Cons((a, b), Cons((c, d), Nil())) => (Cons(a, Cons(c, Nil())), Cons(b, Cons(d, Nil())))
    }
  }
}
