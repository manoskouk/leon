import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object DictFind {

  def dictFind[A, B](l: List[(A, B)], key: A): B = {
    ???[B]
  } ensuring { res =>
    ((l, key), res) passes {
      case (Nil, _) => false
      case (Cons((k, v1), Nil()), v) if v1 == v => true
      case (Cons((k, v1), Nil()), v) if v1 != v => false
      case (Cons((k1, v1), Cons((k2, v2), Nil())), v) if v == v1 => true
      case (Cons((k1, v1), Cons((k2, v2), Nil())), v) if v == v2 => true
      case (Cons((k1, v1), Cons((k2, v2), Nil())), v) if v != v1 && v != v2 => false
    }
  }


}
