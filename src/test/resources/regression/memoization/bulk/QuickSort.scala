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

  def allEq( l : List, pivot : Int) : Boolean = l match {
    case Nil() => true
    case Cons(x,xs) => x == pivot && allEq(xs,pivot)
  }

  // O(n)
  def append(aList:List,bList:List): List = { aList match {
    case Nil() => bList
    case Cons(x, xs) => Cons(x, append(xs,bList))
  }} ensuring { res => contents(res) == contents(aList) ++ contents(bList) }

  // Partition a list in two: 
  // the first contains elements < pivot
  // the second elements = pivot
  // the third elements > pivot
  def partition(pivot : Int, l : List) : (List, List, List) = { l match {
    case Nil() => (Nil(), Nil(), Nil())
    case Cons(x,xs) => 
      val (smaller, equal, greater) = partition(pivot,xs)
      if      (x < pivot)  ( Cons(x,smaller), equal, greater)
      else if (x == pivot) ( smaller, Cons(x,equal), greater)
      else                 ( smaller, equal, Cons(x,greater))     
  }} ensuring { res => res match { case (l1, l2, l3) => 
    //allEq(l2, pivot) &&
    contents(l1) ++ contents(l2) ++ contents(l3) == contents(l)
  }}


  // O(nlogn) average
  def quickSort(list:List): List = { list match {
    case Nil() => Nil()
    case Cons(x,Nil()) => list
    case Cons(x,xs) => 
      val (smaller, equal, greater) = partition(x,xs)
      append( 
        quickSort(smaller), 
        append( 
          Cons(x, equal), 
          quickSort(greater) 
        ) 
      )
  }} ensuring(res => isSorted(res) && contents(res) == contents(list)) 

  def init() : List = Nil()
  def simpleInsert(l:List, i : Int) = Cons(i,l)
  def test(l:List) : List = quickSort(l)

  def main(args : Array[String]) {
    var l = init()
    for (i <- 1 to 10) {
      l = simpleInsert(l,i%7)
    }
    test(l)
  }
}

