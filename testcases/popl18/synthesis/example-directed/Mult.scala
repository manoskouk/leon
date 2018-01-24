import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._

object UnaryNumeralsMult {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  @production(1)
  def nz: Num = Z
  @production(1)
  def ns(n: Num): Num = S(n)
  @production(1)
  def useAdd(x: Num, y: Num) = add(x, y)

  def add(x: Num, y: Num): Num = {
    x match {
      case S(p) => S(add(p, y))
      case Z => y
    }
  } 

  def mult(x: Num, y: Num): Num = {
    ???[Num]
  } ensuring { res =>
    ((x, y), res) passes {
      case (Z, _) => Z
      case (_, Z) => Z
      case (S(Z), S(Z)) => S(Z)
      case (S(S(S(Z))), S(S(Z))) => (S(S(S(S(S(S(Z)))))))
    }
  }
    
}
