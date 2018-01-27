import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object NodesAtLevel {
  abstract class Tree[A]
  case class Leaf[A]() extends Tree[A]
  case class Node[A](l: Tree[A], v: A, r: Tree[A]) extends Tree[A]

  def nodesAtLevel[A](t: Tree[A], l: BigInt): BigInt = {
    require(l >= 0)
    /*(t, l) match {
      case (Leaf(), _) => BigInt(0)
      case (_, BigInt(0)) => BigInt(1)
      case (Node(l, _, r), n) => nodesAtLevel(l, n - 1) + nodesAtLevel(r, n - 1)
    }*/
    ???[BigInt]
  } ensuring { (res: BigInt) =>
    ((t, l), res) passes {
      //case (_, n) if n < 0 => 0
      case (Leaf(), _) => 0
      case (Node(Leaf(), _, Leaf()), BigInt(0)) => 1
      case (Node(Leaf(), _, Leaf()), BigInt(1)) => 0
      case (Node(Leaf(), _, Leaf()), BigInt(2)) => 0
      case (Node(Node(Leaf(), _, Leaf()), _, Leaf()), BigInt(1)) => 1
      case (Node(Node(Leaf(), _, Leaf()), _, Node(Leaf(), _, Leaf())), BigInt(1)) => 2
    }
  }
}
