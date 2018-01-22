import leon.lang._
import leon.annotation.grammar._
import leon.grammar.variable
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object NNF {

  def store(id: BigInt): Boolean = choose { (_: Boolean) => true }

  abstract class Expr
  case class Var(i: BigInt) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Implies(lhs: Expr, rhs: Expr) extends Expr
  case class Not(e: Expr) extends Expr

  abstract class NExpr
  case class NAtom(x: BigInt, neg: Boolean) extends NExpr
  case class NAnd(lhs: NExpr, rhs: NExpr) extends NExpr
  case class NOr(lhs: NExpr, rhs: NExpr) extends NExpr
 
  @production(1)
  def biv(): BigInt = variable[BigInt]
  @production(1)
  def boolt(): Boolean = true
  @production(1)
  def boolf(): Boolean = false

  @production(1)
  def makeEV(): Expr = variable[Expr]

  @production(1)
  def makeNAtom(x: BigInt, neg: Boolean): NExpr = NAtom(x, neg)
  @production(1)
  def makeNAnd(lhs: NExpr, rhs: NExpr): NExpr = NAnd(lhs, rhs)
  @production(1)
  def makeNOr(lhs: NExpr, rhs: NExpr): NExpr = NOr(lhs, rhs)
  @production(1)
  def makeNV(): NExpr = variable[NExpr]
  @production(1)
  def makeWithNeg(e: Expr): NExpr = toNNF(Not(e))

  def eval(e: Expr): Boolean = e match {
    case Var(i) => store(i)
    case Not(e) => !eval(e)
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs) => eval(lhs) || eval(rhs)
    case Implies(lhs, rhs) => !eval(lhs) || eval(rhs)
  }

  def neval(e: NExpr): Boolean = e match {
    case NAtom(x, neg) => if(neg) !store(x) else store(x)
    case NAnd(lhs, rhs) => neval(lhs) && neval(rhs)
    case NOr(lhs, rhs) => neval(lhs) || neval(rhs)
  }

  def toNNF(e: Expr): NExpr = {
    /*
    e match {
      case Var(i) => NAtom(i, false)
      case Not(e1) => e1 match {
        case Var(i) => NAtom(i, true)
        case Not(e2) => toNNF(e2)
        case And(lhs, rhs) => NOr(toNNF(Not(lhs)), toNNF(Not(rhs)))
        case Or(lhs, rhs) => NAnd(toNNF(Not(lhs)), toNNF(Not(rhs)))
        case Implies(lhs, rhs) => NAnd(toNNF(lhs), toNNF(Not(rhs)))
      }
      case And(lhs, rhs) => NAnd(toNNF(lhs), toNNF(rhs))
      case Or(lhs, rhs)  => NOr(toNNF(lhs), toNNF(rhs))
      case Implies(lhs, rhs) => NOr(toNNF(Not(lhs)), toNNF(rhs))
    }*/

    ???
  } ensuring { (ne: NExpr) =>
    neval(ne) == eval(e)
  }

}

