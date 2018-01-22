import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._
//import leon.grammar.Grammar._

object IndexOfPoly {

  def indexOf[A](list: List[A], elem: A): BigInt = {
    ???[BigInt]
  } ensuring { res =>
    ((list, elem), res) passes {
      case (Nil(), _) => -1
      case (Cons(x, _)                  , y) if x == y => 0
      case (Cons(_, Cons(x, _))         , y) if x == y => 1
      case (Cons(_, Cons(_, Cons(x, _))), y) if x == y => 2
    }
  }
  
}
