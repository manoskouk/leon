import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Ins {

  def isSorted(l: List[BigInt]): Boolean = l match {
    case x :: y :: t => x <= y && isSorted(y :: t)
    case _ => true
  }

  def insert(l: List[BigInt], e: BigInt): List[BigInt] = {
    require(isSorted(l))
    conditionally(
      e :: l,
      l.head :: insert(l.tail, e)
    )
  } ensuring { res =>
    res.content == l.content ++ Set(e) &&
    isSorted(res)
  }

}
