import leon.Annotations._

object SortedListSimple {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  @induct
  def size (l : List) : Int = { l match {
    case Nil() => 0
    case Cons(h,t) => 1 + size(t)
  }} ensuring (res => res >= 0 && res > 0)

  def insert(l: List, v: Int): List = {
    require(isSorted(l))

    l match {
      case Nil() => Cons(v, Nil())
      case Cons(x, tail) =>
        if (v < x) {
          Cons(v, l)
        } else if (v == x) {
          l
        } else {
          Cons(x, insert(tail, v))
        }
    }
  } ensuring(isSorted(_))


  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs@Cons(y, _)) => x <= y && isSorted(xs)
  }

  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  
  def test(l : List, i : Int) : List = {
    require(isSorted(l))
    insert(l,i)
  }
  def init() = Nil()
  def main(args : Array[String]) = { 
    val t1 = System.nanoTime
    var t : List = init()
    var i : Int = args(0).toInt
    while (i > 0) {
      t = test(t,psr(i))
      i = i - 1
    }
    val t2 = System.nanoTime
    println( (t2-t1)/1000)
  }
}
