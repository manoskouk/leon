import leon.annotation._
import leon.collection._
import leon.lang.synthesis._
import leon.lang._

object SortedList {
  def isSorted(l: List[Int]): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
  
  def delete[A](l : List[A], v : A) = choose[List[A]](
    _.content == l.content-- Set(v)
  )

  def merge(in1 : List[Int], in2 : List[Int]) = 
    choose[List[Int]] { out =>
      out.content == in1.content ++ in2.content &&
      isSorted(out)
    }
}
