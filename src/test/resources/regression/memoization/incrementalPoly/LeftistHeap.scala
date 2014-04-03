/* Copyright 2009-2013 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._
import leon.annotation._


sealed abstract class Tree[A] {

  def size: Int = { this match {
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



object LeftistHeap {
 
  def max(i1 : Int, i2: Int) : Int = { 
    if (i1 <= i2 ) i1 else i2
  }

  def hasHeapProperty(h : Tree[Int]) : Boolean = h match {
    case Leaf() => true
    case Node(l,v,r) => ( l match {
      case Leaf() => true
      case Node(_,vl,_) => v < vl && hasHeapProperty(l)
    }) && ( r match { 
      case Leaf() => true
      case Node(_,vr,_) => v < vr && hasHeapProperty(r)
    }) 
  }


  def hasLeftistProperty(h: Tree[Int]) : Boolean = (h match {
    case Leaf() => true
    case Node(l, _, r) => hasLeftistProperty(l) && hasLeftistProperty(r) && l.height >= r.height
  })

 
  def removeMax(h: Tree[Int]) : Tree[Int] = {
    require(!h.isEmpty && hasLeftistProperty(h) && hasHeapProperty(h))
    h match {
      case Node(l,v,r) =>  merge(l, r)
    } 
  } ensuring { res => 
    res.size == h.size - 1 &&
    hasLeftistProperty(res) &&
    hasHeapProperty(res)
  }

  def merge(h1: Tree[Int], h2: Tree[Int]) : Tree[Int] = {
    require(
      hasLeftistProperty(h1) && hasLeftistProperty(h2) &&
      hasHeapProperty(h1) && hasHeapProperty(h2)
    )
    (h1, h2) match {
      case (Leaf(), _) => h2
      case (_, Leaf()) => h1
      case (Node(l1, v1, r1), Node(l2, v2, r2)) => 
        if(v1 <= v2) {
          val merged = merge(r1, h2)
          if (l1.height <= merged.height)
            Node(l1, v1, merged)
          else 
            Node(merged, v1, l1)
        }
        else {
          val merged = merge(r2,h1)
          if (l2.height <= l1.height)
            Node(l2, v2, merged)
          else 
            Node(merged, v2, l2)
        }
    }
  } ensuring( res => 
    res.size == h1.size + h2.size &&
    res.height <= h1.height + h2.height &&
    hasLeftistProperty(res) &&
    hasHeapProperty(res)
  )

  def insert(element: Int, heap: Tree[Int]) : Tree[Int] = {
    require(hasLeftistProperty(heap) && hasHeapProperty(heap))
    merge(Node(Leaf(), element,Leaf()), heap)
  } ensuring { res => 
    res.size == heap.size + 1 &&
    hasLeftistProperty(res) &&
    hasHeapProperty(res)
  }

  def init() : Tree[Int] = Leaf()
  @ignore
  def test(h : Tree[Int], i : Int ) : Tree[Int] =                                                                                                                    insert(i,h)


}
     

