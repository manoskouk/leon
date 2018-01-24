import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object RunLength {

  def encode[A](l: List[A]): List[(BigInt, A)] = {
    // Solution
    /*
    l match {
      case Nil() =>
        List[(BigInt, A)]()
      case Cons(h, t) =>
        encode[A](t) match {
          case Nil() =>
            List((BigInt(1), h))
          case Cons(h$1 @ (h_1, h_2), t$1) =>
            if (h == h_2) {
              Cons[(BigInt, A)]((1 + h_1, h_2), t$1)
            } else {
              Cons[(BigInt, A)]((1, h), Cons[(BigInt, A)](h$1, t$1))
            }
        }
    }*/
    ???[List[(BigInt, A)]]
  } ensuring {
    (res: List[(BigInt, A)]) =>
      (l, res) passes {
        case Nil() => Nil()
        case Cons(a, Nil()) => Cons((1,a), Nil())
        case Cons(a, Cons(b, Nil())) if a == b =>
          List((2, a))
        case Cons(a, Cons(b, Cons(c, Nil()))) if a == b && a == c =>
          List((3, a))
        case Cons(a, Cons(b, Cons(c, Nil()))) if a != b && b == c =>
          List((1, a), (2, b))
        case Cons(a, Cons(b, Nil())) if a != b =>
          List((1, a), (1, b))
      }
  }


}
