import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Insert {
  def take[A](l: List[A], n: BigInt) : List[A] = {
    require(n >= 0)
    ???[List[A]]
  } ensuring { (res: List[A]) =>
    ((l, n), res) passes {
      case (Nil(), _) => Nil()
      case (_, BigInt(0)) => Nil()
      case (Cons(a, Cons(b, Nil())), BigInt(1)) => Cons(a, Nil())
      case (Cons(a, Cons(b, Nil())), BigInt(2)) => Cons(a, Cons(b, Nil()))
      case (Cons(a, Cons(b, Nil())), BigInt(5)) => Cons(a, Cons(b, Nil()))
      case (Cons(a, Cons(b, Cons(c, Nil()))), BigInt(2)) => Cons(a, Cons(b, Nil()))
    }
  }
}
