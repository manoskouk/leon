/* Copyright EPFL 2014 */

import leon.lang._
import leon.annotation._


sealed abstract class Color
case object Red   extends Color
case object Black extends Color

sealed abstract class ColoredTree[A] {

  def getColor : Color = this match {
    case Leaf() => Black
    case Node(c, _, _, _) => c
  }

  def size: Int = { this match {
    case Leaf() => 0
    case Node(_, l, _, r) => l.size + 1 + r.size
  }} ensuring (_ >= 0)
 
  // O(n)
  @forceMemo
  def height: Int = { this match {
    case Leaf() => 0
    case Node(_,l, x, r) => {
      val hl = l.height
      val hr = r.height
      if (hl > hr) hl + 1 else hr + 1
    }
  }} ensuring(_ >= 0)
  
  // O(nlogn) assuming balanced
  def content : Set[A] = this match {
    case Leaf() => Set.empty[A]
    case Node(_,l,v,r) => l.content ++ Set[A](v) ++ r.content
  } 
  
  // O(n)
  def balanceFactor : Int = this match {
    case Leaf() => 0
    case Node(_,l, _, r) => l.height - r.height
  }
   

  def isEmpty = this match {
    case Leaf() => true
    case _ => false 
  }
  
  def flip : ColoredTree[A] = this match {
    case Leaf() => Leaf()
    case Node(color,l,e,r) => Node(color, r.flip ,e, l.flip)
  }

} 
  
case class Leaf[A]() extends ColoredTree[A]
case class Node[A](color : Color, left : ColoredTree[A], value : A, right: ColoredTree[A]) extends ColoredTree[A]


object RedBlackTree {
 
  def ins(x : Int, t: ColoredTree[Int]): ColoredTree[Int] = (t match {
    case Leaf() => Node(Red,Leaf(),x,Leaf())
    case Node(c,a,y,b) =>
      if      (x < y)  balance(c, ins(x, a), y, b)
      else if (x == y) Node(c,a,y,b)
      else             balance(c,a,y,ins(x, b))
  }) ensuring (res => 
    (res.content == t.content ++ Set(x)) &&
    (t.size <= res.size && res.size < t.size + 2)
  )

  def add(x: Int, t: ColoredTree[Int]): ColoredTree[Int] = {
    makeBlack(ins(x, t))
  } ensuring (_.content == t.content ++ Set(x))

  def balance(c: Color, a: ColoredTree[Int], x: Int, b: ColoredTree[Int]): ColoredTree[Int] = ( (c,a,x,b) match {
    case (Black,Node(Red,Node(Red,a,xV,b),yV,c),zV,d) =>
      Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
    case (Black,Node(Red,a,xV,Node(Red,b,yV,c)),zV,d) =>
      Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
    case (Black,a,xV,Node(Red,Node(Red,b,yV,c),zV,d)) =>
      Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
    case (Black,a,xV,Node(Red,b,yV,Node(Red,c,zV,d))) =>
      Node(Red,Node(Black,a,xV,b),yV,Node(Black,c,zV,d))
    case (c,a,xV,b) => Node(c,a,xV,b)
  }) ensuring ( _.content == Node(c,a,x,b).content )

  def makeBlack(n: ColoredTree[Int]): ColoredTree[Int] = n match {
    case Node(Red,l,v,r) => Node(Black,l,v,r)
    case _ => n
  }

  
 
}


  
