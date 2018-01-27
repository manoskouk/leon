import leon.lang._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object Calc {
  abstract class Expr 
  case class Const(i: BigInt) extends Expr
  case class Plus(l: Expr, r: Expr) extends Expr
  case class Minus(l: Expr, r: Expr) extends Expr
  case class Times(l: Expr, r: Expr) extends Expr
  case class Max(l: Expr, r: Expr) extends Expr

  def eval(e: Expr): BigInt = {
    ???[BigInt]
  } ensuring { res =>
    (e, res) passes {
      case Const(i) => i
      case Plus(Const(BigInt(8)), Const(BigInt(5))) => 13
      case Minus(Const(BigInt(8)), Const(BigInt(5))) => 3
      case Times(Const(BigInt(8)), Const(BigInt(5))) => 40
      case Max(Const(BigInt(8)), Const(BigInt(5))) => 8
      case Plus(Const(BigInt(-10)), Const(BigInt(7))) => -3
      case Minus(Const(BigInt(-10)), Const(BigInt(7))) => -17
      case Times(Const(BigInt(-10)), Const(BigInt(7))) => -70
      case Max(Const(BigInt(-8)), Const(BigInt(5))) => 5
    }
  }


}
