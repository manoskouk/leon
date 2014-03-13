import leon._
import leon.lang._
import leon.annotation._
import leon.collection._

object SortedList {

  // O(n^2)
  def insertSorted(l: List[Int], v: Int): List[Int] = {
    require(isSorted(l))

    l match {
      case Nil() => Cons(v, Nil())
      case Cons(x, tail) =>
        if (v < x) {
          Cons(v, l)
        } else if (v == x) {
          l
        } else {
          Cons(x, insertSorted(tail, v))
        }
    }
  } ensuring(isSorted(_))


  def deleteSorted(l : List[Int], v : Int) : List[Int] = {
    require(isSorted(l))
    (l match {
      case Nil() => Nil()
      case Cons(h,t) => {
        val newT = deleteSorted(t,v)
        if (h == v) newT else Cons(h, newT)
      }
    }) : List[Int]
  } ensuring { isSorted(_) }


  // O(n)
  def isSorted(l: List[Int]): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs@Cons(y, _)) => x <= y && isSorted(xs)
  }

}
