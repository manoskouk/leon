import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._

object UnaryNumeralsAdd {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  @production(1)
  def nz: Num = Z
  @production(1)
  def ns(n: Num): Num = S(n)

  def add(x: Num, y: Num): Num = {
    ???[Num]
  } ensuring { res =>
    ((x, y), res) passes {
      case (Z, _) => y
      case (_, Z) => x
      case (S(Z), S(Z)) => S(S(Z))
      case (S(S(Z)), S(Z)) => S(S(S(Z)))
    }
  }
}
