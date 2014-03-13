/* Copyright 2009-2013 EPFL, Lausanne 
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._
import leon.collection._
import leon.annotation._
import leon._

sealed abstract class Tree[A] {

  private def size: Int = { this match {
    case Leaf() => 0
    case Node(l, _, r) => l.size + 1 + r.size
  }} ensuring (_ >= 0)
 
  // O(n)
  @forceMemo
  def height: Int = { this match {
    case Leaf() => 0
    case Node(l, x, r) => {
      val hl = l.height
      val hr = r.height
      if (hl > hr) hl + 1 else hr + 1
    }
  }} ensuring(_ >= 0)
  
  // O(nlogn) assuming balanced
  def content : Set[A] = this match {
    case Leaf() => Set.empty[A]
    case Node(l,v,r) => l.content ++ Set[A](v) ++ r.content
  } 
  
  // O(n)
  def balanceFactor : Int = this match {
    case Leaf() => 0
    case Node(l, _, r) => l.height - r.height
  }
   

  def isEmpty = this match {
    case Leaf() => true
    case _ => false 
  }

} 
  
case class Leaf[A]() extends Tree[A]
case class Node[A](left : Tree[A], value : A, right: Tree[A]) extends Tree[A]

object BinaryTrie {
 
  def insert(inp: List[Boolean], t: Tree[Boolean]): Tree[Boolean] = { (inp,t) match {
    
    case ( Cons(x ,xs), Leaf() ) => {
      val newch = insert(xs, Leaf())
      newch match {
        case Leaf() => Node(Leaf(), x, Leaf())
        case Node(_, y, _) => 
          if(y) Node(newch , x, Leaf()) 
          else  Node(Leaf(), x, newch )
      }
    }

    case ( Cons(x,xs@Cons(y, _)), Node(l, v, r) ) => {
      if(y) Node(insert(xs, l), v, r)
      else  Node(l, v, insert(xs, r))
    }

    case _ => t
  
  }} ensuring(res => res.height + t.height >= inp.size)

  def create[T](inp: List[List[Boolean]]) : Tree[Boolean] = { ( inp match {
    case Nil() => Leaf()
    case Cons(h,t) => insert(h, create(t))
  }) : Tree[Boolean] } ensuring { _.height >= inp.size }
}
     

