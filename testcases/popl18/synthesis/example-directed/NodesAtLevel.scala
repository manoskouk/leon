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

  def postorder[A](t: Tree[A], l: BigInt): BigInt = {
    ???[BigInt]
  } ensuring { (res: BigInt) =>
    ((t, l), res) passes {
      case (Leaf(), _) => 0
      case (Node(Leaf(), _, Leaf()), BigInt(0)) => 1
      case (Node(Leaf(), _, Leaf()), BigInt(1)) => 0
      case (Node(Leaf(), _, Leaf()), BigInt(2)) => 0
      case (Node(Node(Leaf(), _, Leaf()), _, Leaf()), BigInt(1)) => 1
      case (Node(Node(Leaf(), _, Leaf()), _, Node(Leaf(), _, Leaf())), BigInt(1)) => 2
    }
  }
}
