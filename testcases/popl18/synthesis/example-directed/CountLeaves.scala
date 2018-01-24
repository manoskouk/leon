import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Postorder {
  abstract class Tree[A]
  case class Leaf[A]() extends Tree[A]
  case class Node[A](l: Tree[A], v: A, r: Tree[A]) extends Tree[A]

  def postorder[A](t: Tree[A]): BigInt = {
    ???[BigInt]
  } ensuring { (res: BigInt) =>
    (t, res) passes {
      case Leaf() => 1
      case Node(Leaf(), _, Leaf()) => 2
      case Node(Node(Leaf(), _, Leaf()), _, Leaf()) => 3
      case Node(Node(Leaf(), _, Leaf()), _, Node(Leaf(), _, Leaf())) => 4
    }
  }
}
