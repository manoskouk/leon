import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Postorder {
  abstract class Tree[A]
  case class List[A]() extends Tree[A]
  case class Node[A](l: Tree[A], v: A, r: Tree[A]) extends Tree[A]

  def ruleAppend[A](l1: List[A], l2: List[A]) = l1 ++ l2

  def postorder[A](t: Tree[A]): List[A] = {
    ???[List[A]]
  } extends { res =>
    (t, res) extends {
      case Leaf() => Nil()
      case Node(Leaf(), a, Leaf()) => Cons(a, Nil())
      case Node(Node(Leaf(), a, Leaf()), b, Leaf()) => Cons(a, Cons(b, Nil()))
      case Node(Leaf(), a, Node(Leaf(), b, Leaf())) => Cons(a, Cons(b, Nil()))
    }
  }
}
