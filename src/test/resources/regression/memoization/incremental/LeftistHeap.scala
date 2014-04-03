/* Copyright 2009-2013 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._
import leon.annotation._

object LeftistHeap {
  sealed abstract class Heap
  case class Leaf() extends Heap
  case class Node(value: Int, left: Heap, right: Heap) extends Heap

  def max(i1 : Int, i2: Int) : Int = { 
    if (i1 <= i2 ) i1 else i2
  }

  @forceMemo
  def height(h: Heap) : Int = {h match {
    case Leaf() => 0
    case Node(_,l,r) => max(height(l), height(r)) + 1 
  }} ensuring(_ >= 0)

  def hasLeftistProperty(h: Heap) : Boolean = (h match {
    case Leaf() => true
    case Node(_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && height(l) >= height(r)
  })

  def size(t: Heap): Int = {
    (t match {
      case Leaf() => 0
      case Node(v, l, r) => size(l) + 1 + size(r)
    })
  }

  def removeMax(h: Heap) : Heap = {
    require(hasLeftistProperty(h))
    h match {
      case Node(_,l,r) => merge(l, r)
      case l @ Leaf() => l
    }
  } ensuring(res => size(res) >= size(h) - 1)

  def merge(h1: Heap, h2: Heap) : Heap = {
    require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
    (h1, h2) match {
      case (Leaf(), _) => h2
      case (_, Leaf()) => h1
      case (Node(v1,l1,r1), Node(v2,l2,r2)) => 
        if(v1 <= v2)
          Node(v1, l1, merge(r1, h2))
        else
          Node(v2, l2, merge(h1, r2))
    }
  } ensuring( res => 
    size(res) == size(h1) + size(h2) &&
    hasLeftistProperty(res)
  )

  /*
  private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
    if(rightHeight(left) >= rightHeight(right))
      Node(rightHeight(right) + 1, value, left, right)
    else
      Node(rightHeight(left) + 1, value, right, left)
  }
*/

  def insert(element: Int, heap: Heap) : Heap = {
    require(hasLeftistProperty(heap))

    merge(Node(element, Leaf(), Leaf()), heap)

  } ensuring( res => 
    size(res) == size(heap) + 1 &&
    hasLeftistProperty(res)
  )

  def init() : Heap = Leaf()
  def test(h : Heap, i : Int ) : Heap = insert(i,h)


}
