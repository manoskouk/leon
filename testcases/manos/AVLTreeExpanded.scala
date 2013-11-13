import leon.Utils._
import leon.Annotations._
import scala.language.postfixOps

object AVLTree  {

  /*
   * Try to prove all functions. Not proven: balance, unbalanced insert.
   * Invariants used: isBST, isAVL
   * Recursive functions called from them: 
   *   isBST, bstMin, bstMax
   *   height(indirectly), isAVL
   */

  /* 
   * create a structure with all these fields
   */
  sealed abstract class TrackedFields
  case class TreeFields(isBST: Boolean, bstMin: OptionInt, bstMax:OptionInt,
                        height: Int, isAVL:Boolean) extends TrackedFields

  /* add this structure to Tree class */
  sealed abstract class Tree
  case class Leaf(fields:TreeFields) extends Tree
  case class Node(left : Tree, value : Int, right: Tree, fields:TreeFields) extends Tree


  /* 
   * Create constructors that obey invariants. 
   * This is based on starting function definitions
   */

  def createLeaf() : Tree = {
    Leaf(TreeFields(true,None(),None(),0, true))
  } ensuring(invariants(_))

  def createNode(left : Tree, value : Int, right: Tree) : Tree = ({
    require(invariants(left) && invariants(right))
    val isBST_ : Boolean = 
      if (isBST(left) && isBST(right)) {
          smallerOption(Some(value),bstMin(right)) && 
          smallerOption(bstMax(left),Some(value))
      }
      else false 
    
    val bstMin_ : OptionInt = left match {
      case Leaf(_) => Some(value) 
      case l       => bstMin(l)
    }

    val bstMax_ : OptionInt = right match {
      case Leaf(_) => Some(value) 
      case r       => bstMax(r)
    }

    val height_ : Int = max(height(left), height(right)) + 1
  
    val isAVL_ : Boolean = 
      isBST_ &&  // Use newly created fields
      {
        // unfold def. of balancefactor
        val balanceFactor_ : Int = height(left) - height(right)
        balanceFactor_ >= -1 && balanceFactor_ <= 1 
      } && 
      isAVL(left) && isAVL(right)  
    
    Node(left,value,right, TreeFields(isBST_, bstMin_, bstMax_, height_, isAVL_))

  }) ensuring(invariants(_))

  
  // Define a function which ensures a Tree was made according to the previous functions

  def invariants(t : Tree) : Boolean = {
    t match {
      case Leaf(_) => 
        t == createLeaf()
      case Node(left, value, right, _) =>
        if (invariants(left) && invariants(right)){
          t == createNode(left, value, right)
        }
        else false
    }
  }
  
  // Define a function which retrieves the tracked fields
  def treeFields(t : Tree) : TreeFields = t match {
    case Leaf(f) => f
    case Node(_,_,_,f) => f
  }


  sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i:Int) extends OptionInt


  def smallerOption(o1:OptionInt,o2:OptionInt) : Boolean  = {
    (o1,o2) match {
      case (Some(i1), Some(i2)) => i1 < i2
      case (_,_) => true
    }
  }

  def minOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1<=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )
  
  def maxOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1>=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )

  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2


    
  
  def treeMax(t:Tree) : OptionInt = {
    t match {
      case Leaf(_)      => None()
      case Node(l,v,r,_) => maxOption(Some(v), maxOption (treeMax(l), treeMax(r)))
    }
  }

  def treeMin(t:Tree) : OptionInt = {
    t match {
      case Leaf(_)      => None()
      case Node(l,v,r,_) => minOption(Some(v), minOption (treeMin(l), treeMin(r)))
    }
  }

  // Change recursive functions to return tracked fields
  def height(t:Tree) = treeFields(t).height
  /*
  def height(t:Tree) : Int = (t match {
    case Leaf() => 0
    case Node(l,_,r) => max(height(l), height(r)) + 1

  }) ensuring(_ >=0)
  */

  def isBST(t:Tree) : Boolean = treeFields(t). isBST
  /*
  def isBST(t:Tree) : Boolean = {
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
  */


  def balanceFactor(t:Tree) : Int = t match {
    case Leaf(_) => 0
    case Node(l,_,r,_) => 
      height(l) - height(r)
  }

  def isAVL(t:Tree) : Boolean = treeFields(t).isAVL
  /*
  def isAVL(t:Tree) : Boolean = {
    isBST(t) && 
    balanceFactor(t) >= -1 &&
    balanceFactor(t) <=  1 &&
    (
      t match {
        case Leaf() => true
        case Node(l,_,r) => 
          isAVL(l) && isAVL(r)  
      }
    )
  }
*/


  def bstMax(t:Tree) : OptionInt = treeFields(t).bstMax
/*  def bstMax(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None() 
      case Node(_,v,Leaf()) => Some(v) 
      case Node(_,_,r)      => bstMax(r)
    }
  } ensuring (_ == treeMax(t))
*/

  def bstMin(t:Tree) : OptionInt = treeFields(t).bstMin
/*
 def bstMin(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None()
      case Node(Leaf(),v,_) => Some(v) 
      case Node(l, _ ,_ ) => bstMin(l)
    }
  } ensuring(_ == treeMin(t))
 */


  /*
   * In the following, replace all constructions of Leaf and Node 
   * with createLeaf and createNode respectively
   */
  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    require(invariants(t) && isAVL(t))
    t match {
      case Leaf(_) => createNode(createLeaf(), e, createLeaf())
      case Node(l,v,r,_) => 
             if (e == v) t
        else if (e <  v) createNode(avlInsert(l,e), v, r)
        else             createNode(l, v, avlInsert(r,e))
    }
  } ensuring(res => invariants(res) && isBST(res) )
                  
  @induct
  def avlInsert(t: Tree, e : Int) : Tree = {
    require(invariants(t) && isAVL(t))
    balance(unbalancedInsert(t,e))
  } ensuring ( res => invariants(res) && isAVL(res) )
   
  @induct
  def balance(t:Tree) : Tree = {
    require( invariants(t) && isBST(t))
    if (isAVL(t)) t
    else t match {
      case Leaf(_) => createLeaf() // impossible...
      case Node(l, v, r, _) => 
        // at this point, the tree is unbalanced
        if(balanceFactor(t) > 1) { // left-heavy
          val newL = 
            if (balanceFactor(l) < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(createNode(newL,v,r))
        }
        else {
          val newR = 
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(createNode(l,v,newR))
        }
    } 
  } ensuring( res => invariants(res) && isAVL(res))

  def rotateRight(t:Tree) = {
    require(invariants(t) && isBST(t))
    t match {
      case Node(Node(ll, vl, rl,_),v,r,_) =>
        createNode(ll, vl, createNode(rl,v,r))  
      case _ => t // this should not happen
  } } ensuring( res => invariants(res) && isBST(res))
   
 
  def rotateLeft(t:Tree) =  {
    require(invariants(t) && isBST(t))
    t match {
      case Node(l, v, Node(lr,vr,rr,_),_) => 
        createNode(createNode(l,v,lr), vr, rr)
      case _ => t // this should not happen
  } } ensuring( res => invariants(res) && isBST(res))

}
    
