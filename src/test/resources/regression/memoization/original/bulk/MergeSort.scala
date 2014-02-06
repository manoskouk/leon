import leon.Utils._
object MergeSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  case class Pair(fst:List, snd:List) 
/*
  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => content(xs) ++ Set(x)
  }
*/
  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(_, Nil()) => true 
    case Cons(x, ys@Cons(y, _)) => x <= y && isSorted(ys)
  }

  def length(list:List): Int = { list match {
    case Nil() => 0
    case Cons(_,xs) => 1 + length(xs)
  }} ensuring( _ >= 0 )

  
  def partition(l : List) : Pair = { l match {
    case Nil()                    => Pair(Nil(), Nil())
    case sing@Cons(_, Nil())      => Pair( sing, Nil())
    case Cons(i1, Cons(i2, tail)) => partition(tail) match {
      case Pair(p1,p2) => Pair( Cons(i1,p1), Cons(i2,p2) )
    }
  }} ensuring { res : Pair => res match { case Pair(l1,l2) =>  
    //content(l1) ++ content(l2) == content(l) &&
     length(l1)  +  length(l2) ==  length(l) 
  }}


  def merge(aList:List, bList:List):List = { 
    require(isSorted(aList) && isSorted(bList))
    (aList, bList) match {
      case ( _, Nil()) => aList
      case ( Nil(), _) => bList
      case ( Cons(x,xs), Cons(y,ys) ) =>
        if (x <= y) Cons(x,merge(xs, bList))
        else        Cons(y,merge(aList, ys))
    }
  } ensuring(res => //content(res) == content(aList) ++ content(bList) && 
    isSorted(res))

  def mergeSort(list:List):List = (list match {
    case Nil() => list
    case Cons(x,Nil()) => list
    case _ => partition(list) match { 
      case Pair(p1,p2) => merge(mergeSort(p1), mergeSort(p2))
    }//split(list,length(list)/2)
  }) ensuring(res => //content(res) == content(list) && 
    isSorted(res)
  )

/*
  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))
    println(ls)
    println(mergeSort(ls))
  }
  // pseudorandom els. to insert
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : List) : List = {
    if (size == 0) acc
    else rec(size -1, Cons(psr(size),acc))
  }
  
  def test(size : Int) : List = { 
      val l = rec(size, Nil())
      mergeSort(l)
  }
  */ 

  def init() : List = Nil()
  def simpleInsert(l:List, i : Int) = Cons(i,l)
  def test(l:List) : List = mergeSort(l)

}


