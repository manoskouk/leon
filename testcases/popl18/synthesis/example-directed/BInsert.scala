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

  def s[A](e: A): Tree[A] = Node(Leaf(), e, Leaf())

  @production(1) def mkLeaf[A](): Tree[A] = Leaf()
  @production(1) def mkNode[A](l: Tree[A], e: A, r: Tree[A]): Tree[A] = Node(l, e, r)

  def insert(t: Tree[BigInt], elem: BigInt): Tree[BigInt] = {
    ???[Tree[BigInt]]
  } ensuring { res =>
    ((t, elem), res) passes {
      case (Leaf(), e) => s(e)
      case (Node(_, a, _), b) if (a == b) =>
        t
      case (Node(Leaf(), a, Leaf()), b) if a < b => Node(Leaf(), a, s(b))
      case (Node(Leaf(), a, Node(Leaf(), b, Leaf())), c) if a < c && b < c =>
        Node(Leaf(), a, Node(Leaf(), b, s(c)))
      case (Node(Leaf(), a, Leaf()), b) if a > b => Node(s(b), a, Leaf())
      case (Node(Leaf(), a, Node(Leaf(), b, Leaf())), c) if a > c && b > c =>
        Node(s(c), a, s(b))
    }
  }
}
