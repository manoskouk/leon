import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object FreeVars {
  abstract class Expr
  case class Var(i: BigInt) extends Expr
  case class Unit() extends Expr
  case class App(f: Expr, a: Expr) extends Expr
  case class Lam(v: BigInt, b: Expr) extends Expr
  case class Let(v: BigInt, vl: Expr, b: Expr) extends Expr

  def fv(e: Expr): Set[BigInt] = {
    ???[Set[BigInt]]
  } ensuring { res =>
    (e, res) passes {
      case Var(i) => Set(i)
      case App(Var(i), Var(j)) => Set(i, j)
      case Lam(BigInt(0), Var(BigInt(0))) => Set()
      case Lam(BigInt(0), Var(BigInt(1))) => Set(BigInt(1))
      case Let(BigInt(0), Var(BigInt(0)), Var(BigInt(1))) => Set(BigInt(0), BigInt(1))
      case Let(BigInt(0), Var(BigInt(1)), Var(BigInt(0))) => Set(BigInt(1))
      case Let(BigInt(0), Var(BigInt(1)), Var(BigInt(2))) => Set(BigInt(1), BigInt(2))
    }
  }
}
