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
  def append(aList:List,bList:List): List = { aList match {
    case Nil() => bList
    case Cons(x, xs) => Cons(x, append(xs,bList))
  }} ensuring { res => contents(res) == contents(aList) ++ contents(bList) }

  def partition(pivot : Int, l : List) : (List, List) = { l match {
    case Nil() => (Nil(), Nil())
    case Cons(x,xs) => 
      val (smaller, greater) = partition(pivot,xs)
      if (x <= pivot) ( Cons(x,smaller) , greater)
      else ( smaller, Cons(x,greater))
  }} ensuring { res => res match { case (l1, l2) => 
    contents(l1) ++ contents(l2) == contents(l)
  }}


  // O(nlogn) average
  def quickSort(list:List): List = { list match {
    case Nil() => Nil()
    case Cons(x,Nil()) => list
    case Cons(x,xs) => 
      val (smaller, greater) = partition(x,xs)
      append( quickSort(append(smaller, Cons(x, Nil()))), quickSort(greater) )
  }} ensuring(res => isSorted(res) && contents(res) == contents(list)) 

  def init() : List = Nil()
  def simpleInsert(l:List, i : Int) = Cons(i,l)
  def test(l:List) : List = quickSort(l)

}

