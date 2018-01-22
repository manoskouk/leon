import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._
import leon.grammar._

object LambdaCalc {

  abstract class Term {
    @inline def apply(arg: Term) = App(this, arg)
  }

  case class V(i: BigInt) extends Term
  case class App(f: Term, a: Term) extends Term
  case class L(b: Term) extends Term

  def abs(i: BigInt) = if (i >= 0) i else -i
  @inline def sign(i: BigInt): BigInt = if (i > 0) 1 else if (i == 0) 0 else -1

  // Taken from:
  // https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture14.pdf
  def shift(i: BigInt, c: BigInt, t: Term): Term = t match {
    case V(n) if abs(n) < c => V(n)
    case V(n) => V(sign(n)* (abs(n) + i))
    case L(e) => L(shift(i, c + 1, e))
    case App(e1, e2) => App(shift(i, c, e1), shift(i, c, e2))
  }

  def subst(t: Term, e: Term, m: BigInt): Term = t match {
    case V(n) if abs(n) == m => e
    case V(n) => V(n)
    case L(e1) => L(subst(e1, shift(1, 0, e), m + 1))
    case App(e1, e2) => App(subst(e1, e, m), subst(e2, e, m))
  }

  // performs η- and β-reduction and simplification within a λ
  def eval(t: Term): Term = t match {
    case App(e10, e20) =>
      (eval(e10), eval(e20)) match {
        case (L(e1), e2) =>        
          shift(-1, 0, subst(e1, shift(1, 0, e2), 0))
        case (e1, e2) => App(e1, e2)
      }
    case L( App(t, V(BigInt(0))) ) =>
      eval(shift(1, 0, t))
    case L(t) =>
      L(eval(t))
    case V(n) =>
      V(n)
  }

  val T = L(L(V(1)))
  val F = L(L(V(0)))

  @production(5) def v(i: BigInt): Term = V(i)
  @production(5) def app(f: Term, a: Term): Term = App(f, a)
  @production(5) def abs(b: Term): Term = L(b)
  @production(2) def tp(): Term = T
  @production(2) def fp(): Term = F
  @production(5) def vp(): Term = variable[Term]
  @production(3) def i0(): BigInt = BigInt(0)
  @production(3) def i1(): BigInt = BigInt(1)
  @production(2) def i2(): BigInt = BigInt(2)
  @production(1) def i3(): BigInt = BigInt(3)

  def notSpec(arg: Term, nt: Term): Boolean = eval(arg) match {
    case ea if ea == T =>
      eval(nt(arg)) == F
    case ea if ea == F =>
      eval(nt(arg)) == T
    case _ => true
  }

  def not(t: Term) = {
    ???[Term]
  } ensuring { res =>
    (eval(t) == T) ==> (eval(res) == F) &&
    (eval(t) == F) ==> (eval(res) == T)
  }

  def and(t1: Term, t2: Term) = {
    ???[Term]
  } ensuring { res => 
    (eval(t1) == F) ==> (eval(res) == F) &&
    (eval(t1) == T && eval(t2) == T) ==> (eval(res) == T) &&
    (eval(t1) == T && eval(t2) == F) ==> (eval(res) == F)
  }

  def ite(cond: Term, thenn: Term, elze: Term) = {
    //App(App(cond, thenn), elze)
    ???[Term]
  } ensuring { (res: Term) =>
    (cond == T) ==> (eval(res) == eval(thenn)) &&
    (cond == F) ==> (eval(res) == eval(elze))
  }

  //  val N0 = L(L(V(0)))
  def chEnc(n: BigInt): Term = {
    require(n >= 0)
    def apps(n: BigInt): Term = if (n == 0) V(0) else V(1)(apps(n-1))
    L(L(apps(n)))
  }

  def value(t: Term): Option[BigInt] = t match {
    case L(L(apps)) =>
      def countApps(t: Term): Option[BigInt] = t match {
        case V(BigInt(0)) => Some(0)
        case App(V(BigInt(1)), t1) => countApps(t1) map (_ + 1)
        case _ => None()
      }
      countApps(apps)

    case _ => None()
  }

  def isN(t: Term, n: BigInt): Boolean = {
    val v = value(t)
    v.isDefined && v.get == n
  }

  val N0 = choose((t: Term) => isN(t, 0))
  val N1 = choose((t: Term) => isN(t, 1))
  val N2 = choose((t: Term) => isN(t, 2))
  val N3 = choose((t: Term) => isN(t, 3))
  val N4 = choose((t: Term) => isN(t, 4))
  val N5 = choose((t: Term) => isN(t, 5))

  @inline def V0 = V(0)
  @inline def V1 = V(1)
  @inline def V2 = V(2)
  @inline def V3 = V(3)

  def add(t1: Term, t2: Term) = {
    require(value(t1).isDefined && value(t2).isDefined)
    // L(L( App ( App(t1, V(1)), App(App(t2, V(1)), V(0))) ))
    ???[Term]
  } ensuring { res =>
    val vR = value(res)
    vR.isDefined && vR.get == value(t1).get + value(t2).get
  }

  def succ(t: Term) = {
    require(value(eval(t)).isDefined)
    // L(L(V1( t(V1)(V0) ) ))
    ???[Term]
  } ensuring { res =>
    val v = value(eval(res))
    v.isDefined && v.get == value(eval(t)).get + 1
  }
}




