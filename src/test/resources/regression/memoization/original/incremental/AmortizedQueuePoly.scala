// reverse is not implemented tail-recursively! :(

// Problems : content

import leon.lang._
import leon.annotation._
import leon.collection._
import leon._


case class AmortizedQueue[A](private val front : List[A], private val rear : List[A]) {
  import AmortizedQueueOps._

  def size : Int = { front.size + rear.size } ensuring ( _ >= 0 )
  
  def content : Set[A] = front.content ++ rear.content

  def isEmpty : Boolean = { (front,rear) match {
    case (Nil(), Nil()) => true
    case _ => false
  }} ensuring ( _ == this.toList.isEmpty )

  def toList : List[A] = {
    front ++ rear.reverse
  } ensuring ( _.content == this.content )
  
  def isAmortized : Boolean = front.size >= rear.size

  def enqueue(elem : A) : AmortizedQueue[A] =  {
    amortizedQueue(front, Cons(elem, rear))
  } ensuring ( res => 
    res.isAmortized && 
    res.toList == this.toList :+ elem
  )
/*
  def push(elem : A) : AmortizedQueue[A] = {
    amortizedQueue(Cons(elem,front), rear)
  } ensuring ( res => 
    res.isAmortized && 
    res.toList == Cons(elem, this.toList)
  )
*/    

  def head : A = {
    require(isAmortized && !isEmpty)
    front.head
  } ensuring ( _ == this.toList.head )


  def tail : AmortizedQueue[A] = {
    require(isAmortized && !isEmpty)
    amortizedQueue(front.tail, rear)
  } ensuring ( res => 
    res.isAmortized &&
    res.toList == this.toList.tail
  )

  def dequeue : (A, AmortizedQueue[A]) = {
    require(isAmortized && !isEmpty)
    (this.head, this.tail) 
  } ensuring { res =>
    val (f,q) = res
    q.isAmortized && Cons(f, q.toList) == this.toList
  }

  def headOption : Option[A]        = if (!isEmpty) Some(this.head) else None()
  def tailOption : Option[AmortizedQueue[A]] = if (!isEmpty) Some(this.tail) else None()

}


object AmortizedQueueOps {

  def emptyQueue[T]() : AmortizedQueue[T] = AmortizedQueue[T](Nil[T](), Nil[T]())

  def amortizedQueue[A](front : List[A], rear : List[A]) : AmortizedQueue[A] = {
    if (rear.size <= front.size)
      AmortizedQueue(front, rear)
    else
      AmortizedQueue(front ++ rear.reverse, Nil[A]())
  } ensuring ( res => 
    res.isAmortized && 
    AmortizedQueue(front, rear).toList == res.toList
  )

  

  // For memo testing
  @ignore
  def test[A](q:AmortizedQueue[A], i:A) : AmortizedQueue[A] = q.enqueue(i)
  @ignore
  def init[Tp]() : AmortizedQueue[Tp] = emptyQueue[Tp]()

}

object AmortizedQueueProps {

  import AmortizedQueueOps._
  // @induct
  // def propEnqueue(rear : List, front : List, list : List, elem : Int) : Boolean = {
  //   require(isAmortized(AmortizedQueue(front, rear)))
  //   val queue = AmortizedQueue(front, rear)
  //   if (q2l(queue) == list) {
  //     q2l(enqueue(queue, elem)) == concat(list, Cons(elem, Nil()))
  //   } else
  //     true
  // } holds

  @induct
  def propHead[A](queue : AmortizedQueue[A], list : List[A] ) : Boolean = {
    require(!queue.isEmpty && queue.isAmortized && queue.toList == list )
    list.head == queue.head  
  } holds

  @induct
  def propTail[A](queue : AmortizedQueue[A], list : List[A]) : Boolean = {
    require( !queue.isEmpty && queue.isAmortized && queue.toList == list )
    list.tail == queue.tail.toList
  } holds

  /*
  def enqueueAndHead[A](queue : AmortizedQueue[A], elem : A) : Boolean = {
    require(queue.isEmpty)
    queue.enqueue(elem).head == elem
  } holds
*/

  def enqueueDequeueThrice[A](e1 : A, e2 : A, e3 : A) : Boolean = {
    val q1 = emptyQueue().enqueue(e1)
    val q2 = q1.enqueue(e2)
    val q3 = q2.enqueue(e3)
    val (e1prime, q4) = q3.dequeue
    val (e2prime, q5) = q4.dequeue
    val (e3prime, q6) = q5.dequeue
    e1 == e1prime && e2 == e2prime && e3 == e3prime
  } holds
  

 
}
