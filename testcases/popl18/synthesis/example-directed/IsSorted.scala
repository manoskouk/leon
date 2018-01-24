import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object IsSorted {

  def isSorted(l: List[Int]): Boolean = {
    ???[Boolean]
  } ensuring { res =>
    (l, res) passes {
      case Nil() => true
      case Cons(_, Nil()) => true
      case Cons(0, Cons(1, Nil())) => true
      case Cons(1, Cons(-1, Nil())) => false
      case Cons(0, Cons(0, Nil())) => true
      case Cons(0, Cons(1, Cons(42, Nil()))) => true
      case Cons(0, Cons(88, Cons(42, Nil()))) => false
    }
  }


}
