import scala.collection.immutable.Set

//problem with content

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  // O(n)
  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  // O(n)
  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x,Nil()) => true
    case Cons(x,xs@Cons(y,ys)) => x<=y && isSorted(xs)
  }

  // O(n)
  def rev_append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case Cons(x,xs) => rev_append(xs,Cons(x,bList))
  }

  // O(n)
  def reverse(list:List): List = rev_append(list,Nil())

  // O(n)
  def append(aList:List,bList:List): List = aList match {
    case Nil() => bList
    case _ => rev_append(reverse(aList),bList)
  }

  def greater(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n < x) Cons(x,greater(n,xs)) else greater(n,xs)
  }

  def smaller(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n>x) Cons(x,smaller(n,xs)) else smaller(n,xs)
  }

  def equals(n:Int,list:List) : List = list match {
    case Nil() => Nil()
    case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)
  }

  // O(nlogn) average
  def quickSort(list:List): List = (list match {
    case Nil() => Nil()
    case Cons(x,Nil()) => list
    case Cons(x,xs) => append(append(quickSort(smaller(x,xs)),Cons(x,equals(x,xs))),quickSort(greater(x,xs)))
  }) ensuring(res => isSorted(res) && contents(res) == contents(list)) 
/*
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(quickSort(ls))
  }

  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : List) : List = {
    if (size == 0) acc
    else rec(size -1, Cons(psr(size),acc))
  }
  
  def test(size : Int) : List = { 
      val l = rec(size, Nil())
      quickSort(l)
  }
*/


  def init() : List = Nil()
  def simpleInsert(l:List, i : Int) = Cons(i,l)
  def test(l:List) : List = quickSort(l)

}

