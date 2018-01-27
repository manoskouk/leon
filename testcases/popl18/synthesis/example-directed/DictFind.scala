import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object DictFind {

  def dictFind[A, B](l: List[(A, B)], key: A): Option[B] = {
    ???[Option[B]]
  } ensuring { res =>
    ((l, key), res) passes {
      case (Nil(), _) => None()
      case (Cons((k1, v1), Nil()), k) if k == k1 => Some(v1)
      case (Cons((k1, v1), Nil()), k) if k != k1 => None()
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k) if k == k1 => Some(v1)
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k) if k != k1 && k == k2 => Some(v2)
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k) if k != k1 && k != k2 => None()
    }
  }


}
