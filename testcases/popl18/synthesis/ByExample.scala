import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object ByExample {
  def size[A](l: List[A]): BigInt = {
    ???
  } ensuring { (res: BigInt) =>
    (l, res) passes {
      case Nil() => 0
      case Cons(a, Nil()) => 1
      case Cons(a, Cons(b, Nil())) => 2
    }
  }

  def content[A](l: List[A]): Set[A] = {
    ???
  } ensuring { (res: Set[A]) =>
    (l,res) passes {
      case Nil() => Set[A]()
      case Cons(a, Nil()) => Set[A](a)
    }
  }

}
