import leon.lang._
import leon.lang.synthesis._

object BatchedQueue {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty
    case Cons(head, tail) => Set(head) ++ content(tail)
  }

  def content(p: Queue): Set[Int] =
    content(p.f) ++ content(p.r)

  def isEmpty(p: Queue): Boolean = p.f == Nil

  case class Queue(f: List, r: List)

  def rev_append(aList: List, bList: List): List = (aList match {
    case Nil => bList
    case Cons(x, xs) => rev_append(xs, Cons(x, bList))
  }) ensuring (content(_) == content(aList) ++ content(bList))

  def reverse(list: List) = rev_append(list, Nil) ensuring (content(_) == content(list))
  	  
  def queueInvariant(q:Queue) = if (q.f == Nil) q.r == Nil else true
  
  	  def invariantList(q:Queue, f: List, r: List): Boolean = {
  	  	rev_append(q.f, q.r) == rev_append(f, r) &&
  	    { if (q.f == Nil) q.r == Nil else true }
  }

  def checkf(f: List, r: List): Queue = (f match {
    case Nil => Queue(reverse(r), Nil)
    case _ => Queue(f, r)
  }) ensuring {
    res => content(res) == content(f) ++ content(r)
  }
  //	  
  //	  def last(p: Queue): Int = {
  //	    require(!isEmpty(p))
  //	    p.r match {
  //	      case Nil => reverse(p.f).asInstanceOf[Cons].head
  //	      case Cons(x, _) => x
  //	    }
  //	  }

  def snoc(p: Queue, x: Int): Queue = {
    require(queueInvariant(p))
    choose { (res: Queue) =>
      content(res) == content(p) ++ Set(x) &&
        {res.f match {
		      case Nil => content(res) ++ Set(x) == content(res)
		      case Cons(_, xs) =>
          	content(checkf(xs, p.r)) ++ Set(x) == content(checkf(xs, p.r))
		    }}
         
    }
  }
}
