import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Merge {

  def isSorted(l: List[BigInt]): Boolean = l match {
    case x :: y :: t => x <= y && isSorted(y :: t)
    case _ => true
  }

  def merge(l1 : List[BigInt], l2 : List[BigInt]) : List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    conditionally(
      Nil[BigInt](),
      l1.head :: merge(l1.tail, l2),
      l2.head :: merge(l1, l2.tail)
    )
  } ensuring { res =>
    isSorted(res) &&
    res.size == l1.size + l2.size &&
    res.content == l1.content ++ l2.content
  }

}
