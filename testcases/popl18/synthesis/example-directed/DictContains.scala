import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object DictReplace {

  def dictReplace[A, B](l: List[(A, B)], key: A, v: B): List[(A,B)] = {
    ???[List[(A, B)]]
  } ensuring { res =>
    ((l, key, v), res) passes {
      case (Nil(), _, _) => Nil()
      case (Cons((k1, v1), Nil()), k, v) if k == k1 => List((k1, v))
      case (Cons((k1, v1), Nil()), k, v) if k != k1 => l
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k, v) if k != k1 && k == k2 =>
        List((k1, v1), (k2, v))
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k, v) if k != k1 && k != k2 =>
        List((k1, v1), (k2, v2))
      case (Cons((k1, v1), Cons((k2, v2), Nil())), k, v) if k == k1 && k == k2 =>
        List((k1, v), (k2, v))
    }
  }


}
