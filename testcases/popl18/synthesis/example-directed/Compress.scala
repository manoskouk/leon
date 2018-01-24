import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object Compress {

  def compress[A](l: List[A]): List[A] = {
    // Solution
    ???[List[A]]
  } ensuring {
    (res: List[A]) =>
      (l, res) passes {
        case Nil() => Nil()
        case Cons(a, Nil()) => List(a)
        case Cons(a, Cons(b, Nil())) if a == b =>
          List(a)
        case Cons(a, Cons(b, Nil())) if a != b =>
          List(a, b)
        case Cons(a, Cons(b, Cons(c, Nil()))) if a == b && a == c =>
          List(a)
        case Cons(a, Cons(b, Cons(c, Nil()))) if a != b && b == c =>
          List(a, b)
      }
  }


}
