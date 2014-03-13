/* Copyright 2009-2013 EPFL, Lausanne 
 *
 * Author: Manos (modified by Ravi)
 * Date: 20.11.2013
 **/

import leon._
import leon.lang._
import leon.annotation._ 
import leon.collection._


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




// Sorted/avl tree specific stuff
object AVLTree  {

  def smallerOption(o1:Option[Int],o2:Option[Int]) : Boolean  = {
    (o1,o2) match {
      case (Some(i1), Some(i2)) => i1 < i2
      case (_,_) => true
    }
  }

  def minOption(o1:Option[Int],o2:Option[Int]) : Option[Int] = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1<=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )
  
  def maxOption(o1:Option[Int],o2:Option[Int]) : Option[Int] = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1>=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )

  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2

  def treeMax(t:Tree[Int]) : Option[Int] = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => maxOption(Some(v), maxOption (treeMax(l), treeMax(r)))
    }
  }

  def treeMin(t:Tree[Int]) : Option[Int] = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => minOption(Some(v), minOption (treeMin(l), treeMin(r)))
    }
  }

  
  def isBST(t:Tree[Int]) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        if (isBST(l) && isBST(r)) {
          smallerOption(Some(v),bstMin(r)) && 
          smallerOption(bstMax(l),Some(v))
        }
        else false 
    }
  }

   
  // O(nlogn) assuming balanced trees
  def isAVL(t:Tree[Int]) : Boolean = {    
    t match {
        case Leaf() => true        
        case Node(l,v,r) =>  
          isAVL(l) && isAVL(r) && 
          smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) &&
          t.balanceFactor >= -1 && t.balanceFactor <= 1 
      }    
  } 

  def bstMax(t:Tree[Int]) : Option[Int] = {
    require(isBST(t))
    ( t match {
      case Leaf() => None() 
      case Node(_,v,Leaf()) => Some(v) 
      case Node(_,_,r)      => bstMax(r)
    } ) : Option[Int]
  } ensuring (res => res == treeMax(t))

  def bstMin(t:Tree[Int]) : Option[Int] = {
    require(isBST(t))
    ( t match {
      case Leaf() => None()
      case Node(Leaf(),v,_) => Some(v) 
      case Node(l,     _,_) => bstMin(l)
    } ) : Option[Int]
  } ensuring (res => res == treeMin(t))
  
  // O(nlogn)
  def offByOne(t : Tree[Int]) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        isAVL(l) && isAVL(r) && 
        t.balanceFactor >= -2 && t.balanceFactor <= 2 &&
        smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) 
    }
  }

  // T1(n) = O(nlogn) + T2(n/2)  
  // O(nlogn)
  @induct
  def unbalancedInsert(t: Tree[Int], e : Int) : Tree[Int] = {
    require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf())
      case Node(l,v,r) => 
             if (e == v) t
        else if (e <  v){
          val newl = avlInsert(l,e)
          Node(newl, v, r)
        } 
        else {
          val newr = avlInsert(r,e)
          Node(l, v, newr)
        }            
    }
  } ensuring(res => offByOne(res) && res.content == t.content ++ Set[Int](e))
             
  // T2(n) = O(nlogn) + T1(n) 
  // O(nlogn)
  def avlInsert(t: Tree[Int], e : Int) : Tree[Int] = {    
    require(isAVL(t))
    
    balance(unbalancedInsert(t,e))
    
  } ensuring(res => 
    isAVL(res) && 
    res.height >= t.height && 
    res.height <= t.height + 1 && 
    res.size <= t.size + 1 &&
    res.content == t.content ++ Set[Int](e)
  )
     
  // O(nlogn)
  def balance(t:Tree[Int]) : Tree[Int] = {
    require(offByOne(t) && !t.isEmpty) //isBST(t) && 
    t match {
      case Node(l, v, r) => 
        val bfactor = t.balanceFactor
        // at this point, the tree is unbalanced
        if(bfactor > 1 ) { // left-heavy
          val newL = 
            if (l.balanceFactor < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(Node(newL,v,r))
        }
        else if(bfactor < -1) { //right-heavy
          val newR = 
            if (r.balanceFactor > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR))
        } else t        
      } 
    } ensuring(res => isAVL(res) && res.content == t.content)

  def rotateRight(t:Tree[Int]) : Tree[Int]= {    
    t match {
      case Node(Node(ll, vl, rl),v,r) =>
        
        val hr = max(rl.height,r.height) + 1        
        Node(ll, vl, Node(rl,v,r))
        
      case _ => error[Tree[Int]]("Rotating a tree of the wrong form!") 
  } }
   
 
  def rotateLeft(t:Tree[Int]) : Tree[Int]=  {    
    t match {
      case Node(l, v, Node(lr,vr,rr)) => 
                
        val hl = max(l.height, lr.height) + 1        
        Node(Node(l,v,lr), vr, rr)
      case _ => error[Tree[Int]]("Rotating a tree of the wrong form!") 
  } } 

 
}


