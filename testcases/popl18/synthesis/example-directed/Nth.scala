import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Nth {

  def nth[A](l:List[A], n: BigInt): A = {
    require(l.size > n)
    ???[A]
  } ensuring { res =>
    ((l, n), res) passes {
      case (Cons(a, Nil()), BigInt(0)) => a
      case (Cons(a, Cons(b, Nil())), BigInt(0)) => a
      case (Cons(a, Cons(b, Nil())), BigInt(1)) => b
    }
  }

}
