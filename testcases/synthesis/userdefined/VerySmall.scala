package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import annotation.grammar._

object SmallGrammar {

  @production(5062)
  def pBooleanVariable$0(): Boolean = variable[Boolean]

  @production(960)
  def pBooleanAnd$0(v0$0 : Boolean, v1$7 : Boolean): Boolean = v0$0 && v1$7

  @production(565)
  def pBooleanBooleanLiteral$0(): Boolean = true

  @production(214)
  def pBooleanBooleanLiteral$1(): Boolean = false

  @production(328)
  def pBooleanEquals$0(v0$1 : BigInt, v1$8 : BigInt): Boolean = v0$1 == v1$8

  @production(75)
  def pBooleanEquals$3(v0$4 : Boolean, v1$11 : Boolean): Boolean = v0$4 == v1$11

  @production(1292)
  def pBooleanGreaterEquals$0(v0$5 : BigInt, v1$12 : BigInt): Boolean = v0$5 >= v1$12

  @production(458)
  def pBooleanNot$0(v0$7 : Boolean): Boolean = !v0$7

  @production(211)
  def pBooleanLessThan$0(v0$8 : BigInt, v1$14 : BigInt): Boolean = v0$8 < v1$14

  @production(257)
  def pBooleanIfExpr$0(v0$12 : Boolean, v1$18 : Boolean, v2$9 : Boolean): Boolean = if (v0$12) {
    v1$18
  } else {
    v2$9
  }

  @production(124)
  def pBooleanOr$0(v0$15 : Boolean, v1$21 : Boolean): Boolean = v0$15 || v1$21

  @production(46)
  def pBooleanImplies$0(v0$16 : Boolean, v1$22 : Boolean): Boolean = v0$16 ==> v1$22

  @production(2445)
  def pBigIntVariable$0(): BigInt = variable[BigInt]

  @production(649)
  def pBigIntInfiniteIntegerLiteral$0(): BigInt = BigInt(0)

  @production(325)
  def pBigIntInfiniteIntegerLiteral$1(): BigInt = BigInt(1)

  @production(94)
  def pBigIntInfiniteIntegerLiteral$2(): BigInt = BigInt(2)

  @production(19)
  def pBigIntInfiniteIntegerLiteral$3(): BigInt = BigInt(10)

  @production(13)
  def pBigIntInfiniteIntegerLiteral$4(): BigInt = BigInt(5)

  @production(12)
  def pBigIntInfiniteIntegerLiteral$5(): BigInt = BigInt(60)

  @production(9)
  def pBigIntInfiniteIntegerLiteral$6(): BigInt = BigInt(4)

  @production(6)
  def pBigIntInfiniteIntegerLiteral$7(): BigInt = BigInt(6)

  @production(6)
  def pBigIntInfiniteIntegerLiteral$8(): BigInt = BigInt(3)

  @production(6)
  def pBigIntInfiniteIntegerLiteral$9(): BigInt = BigInt(-1)

  @production(5)
  def pBigIntInfiniteIntegerLiteral$10(): BigInt = BigInt(7)

  @production(5)
  def pBigIntInfiniteIntegerLiteral$11(): BigInt = BigInt(-2)

  @production(4)
  def pBigIntInfiniteIntegerLiteral$12(): BigInt = BigInt(3600)

  @production(4)
  def pBigIntInfiniteIntegerLiteral$13(): BigInt = BigInt(50)

  @production(3)
  def pBigIntInfiniteIntegerLiteral$14(): BigInt = BigInt(32)

  @production(3)
  def pBigIntInfiniteIntegerLiteral$15(): BigInt = BigInt(8)

  @production(2)
  def pBigIntInfiniteIntegerLiteral$16(): BigInt = BigInt(35)

  @production(2)
  def pBigIntInfiniteIntegerLiteral$17(): BigInt = BigInt(30)

  @production(2)
  def pBigIntInfiniteIntegerLiteral$18(): BigInt = BigInt(100)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$19(): BigInt = BigInt(1001)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$20(): BigInt = BigInt(-3)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$21(): BigInt = BigInt(53)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$22(): BigInt = BigInt(13)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$23(): BigInt = BigInt(17)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$24(): BigInt = BigInt(59)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$25(): BigInt = BigInt(-10)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$26(): BigInt = BigInt(31)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$27(): BigInt = BigInt(40)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$28(): BigInt = BigInt(300)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$29(): BigInt = BigInt(15)

  @production(1)
  def pBigIntInfiniteIntegerLiteral$30(): BigInt = BigInt(200)

  @production(245)
  def pBigIntMinus$0(v0$30 : BigInt, v1$35 : BigInt): BigInt = v0$30 - v1$35

  @production(187)
  def pBigIntPlus$0(v0$31 : BigInt, v1$36 : BigInt): BigInt = v0$31 + v1$36

  @production(116)
  def pBigIntTimes$0(v0$32 : BigInt, v1$37 : BigInt): BigInt = v0$32 * v1$37

  @production(5046)
  def pBigIntIfExpr$0(v0$33 : Boolean, v1$38 : BigInt, v2$11 : BigInt): BigInt = if (v0$33) {
    v1$38
  } else {
    v2$11
  }

  @production(32)
  def pBigIntDivision$0(v0$34 : BigInt, v1$39 : BigInt): BigInt = v0$34 / v1$39

  @production(23)
  def pBigIntUMinus$0(v0$35 : BigInt): BigInt = -v0$35

  @production(18)
  def pBigIntRemainder$0(v0$36 : BigInt, v1$40 : BigInt): BigInt = v0$36 % v1$40

}
