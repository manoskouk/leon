import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._

object UnaryNumeralsAdd {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def isEven(x: Num): Boolean = {
    ???[Boolean]
  } ensuring { res =>
    (x, res) passes {
      case Z => true
      case S(Z) => false
      case S(S(Z)) => true
    }
  }
}
