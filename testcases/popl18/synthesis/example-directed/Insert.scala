import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object SortedListInsert {
 
  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, t@Cons(x2, _)) => x1 < x2 && isSorted(t)
    case _ => true
  }

  def insert(in: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(in))

    choose { (out : List[BigInt]) =>
      ((in, v), out) passes {
        case (Nil(), v) => List(v)
        case (Cons(a, Nil()), b) if a == b => in
        case (Cons(BigInt(1), Nil()), BigInt(2)) => List(1, 2)
        case (Cons(BigInt(1), Nil()), BigInt(-22)) => List(-22, 1)
        case (Cons(BigInt(42), Nil()), BigInt(-22)) => List(-22, 42)
        case (Cons(BigInt(1), Cons(BigInt(42), Nil())), BigInt(100)) => List(1, 42, 100)
      }
    }
  }
}
