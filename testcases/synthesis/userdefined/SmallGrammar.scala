package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import annotation.grammar._

object SmallGrammar {

  @production(1062)
  def pBooleanVariable$0(): Boolean = variable[Boolean]

  @production(960)
  def pBooleanAnd$0(v0$0 : Boolean, v1$7 : Boolean): Boolean = v0$0 && v1$7

  @production(565)
  def pBooleanBooleanLiteral$0(): Boolean = true

  @production(214)
  def pBooleanBooleanLiteral$1(): Boolean = false

  @production(328)
  def pBooleanEquals$0(v0$1 : BigInt, v1$8 : BigInt): Boolean = v0$1 == v1$8

  @production(244)
  def pBooleanEquals$1(v0$2 : Int, v1$9 : Int): Boolean = v0$2 == v1$9

  @production(75)
  def pBooleanEquals$3(v0$4 : Boolean, v1$11 : Boolean): Boolean = v0$4 == v1$11

  @production(173)
  def pBooleanGreaterEquals$0(v0$5 : BigInt, v1$12 : BigInt): Boolean = v0$5 >= v1$12

  @production(411)
  def pBooleanGreaterEquals$1(v0$6 : Int, v1$13 : Int): Boolean = v0$6 >= v1$13

  @production(458)
  def pBooleanNot$0(v0$7 : Boolean): Boolean = !v0$7

  @production(98)
  def pBooleanLessThan$0(v0$8 : BigInt, v1$14 : BigInt): Boolean = v0$8 < v1$14

  @production(332)
  def pBooleanLessThan$1(v0$9 : Int, v1$15 : Int): Boolean = v0$9 < v1$15

  @production(119)
  def pBooleanLessEquals$0(v0$10 : BigInt, v1$16 : BigInt): Boolean = v0$10 <= v1$16

  @production(183)
  def pBooleanLessEquals$1(v0$11 : Int, v1$17 : Int): Boolean = v0$11 <= v1$17

  @production(257)
  def pBooleanIfExpr$0(v0$12 : Boolean, v1$18 : Boolean, v2$9 : Boolean): Boolean = if (v0$12) {
    v1$18
  } else {
    v2$9
  }

  @production(113)
  def pBooleanGreaterThan$0(v0$13 : BigInt, v1$19 : BigInt): Boolean = v0$13 > v1$19

  @production(109)
  def pBooleanGreaterThan$1(v0$14 : Int, v1$20 : Int): Boolean = v0$14 > v1$20

  @production(124)
  def pBooleanOr$0(v0$15 : Boolean, v1$21 : Boolean): Boolean = v0$15 || v1$21

  @production(46)
  def pBooleanImplies$0(v0$16 : Boolean, v1$22 : Boolean): Boolean = v0$16 ==> v1$22

  @production(3460)
  def pIntVariable$0(): Int = variable[Int]

  @production(828)
  def pIntIntLiteral$0(): Int = 0

  @production(387)
  def pIntIntLiteral$1(): Int = 1

  @production(87)
  def pIntIntLiteral$2(): Int = 2

  @production(46)
  def pIntIntLiteral$3(): Int = -1

  @production(43)
  def pIntIntLiteral$4(): Int = 5

  @production(25)
  def pIntIntLiteral$5(): Int = 3

  @production(12)
  def pIntIntLiteral$6(): Int = 32

  @production(8)
  def pIntIntLiteral$7(): Int = 4

  @production(4)
  def pIntIntLiteral$8(): Int = 10

  @production(4)
  def pIntIntLiteral$9(): Int = 33

  @production(4)
  def pIntIntLiteral$10(): Int = -2

  @production(3)
  def pIntIntLiteral$11(): Int = 31

  @production(2)
  def pIntIntLiteral$12(): Int = 1073741824

  @production(2)
  def pIntIntLiteral$13(): Int = 6

  @production(2)
  def pIntIntLiteral$14(): Int = 7

  @production(1)
  def pIntIntLiteral$15(): Int = 42

  @production(1)
  def pIntIntLiteral$16(): Int = 349

  @production(1)
  def pIntIntLiteral$17(): Int = -1000

  @production(1)
  def pIntIntLiteral$18(): Int = -10

  @production(1)
  def pIntIntLiteral$19(): Int = 100000000

  @production(1)
  def pIntIntLiteral$20(): Int = -33

  @production(1)
  def pIntIntLiteral$21(): Int = 358

  @production(1)
  def pIntIntLiteral$22(): Int = 122

  @production(304)
  def pIntBVPlus$0(v0$17 : Int, v1$23 : Int): Int = v0$17 + v1$23

  @production(101)
  def pIntBVMinus$0(v0$18 : Int, v1$24 : Int): Int = v0$18 - v1$24

  @production(41)
  def pIntIfExpr$0(v0$19 : Boolean, v1$25 : Int, v2$10 : Int): Int = if (v0$19) {
    v1$25
  } else {
    v2$10
  }

  @production(20)
  def pIntBVTimes$0(v0$20 : Int, v1$26 : Int): Int = v0$20 * v1$26

  @production(10)
  def pIntBVAShiftRight$0(v0$21 : Int, v1$27 : Int): Int = v0$21 >> v1$27

  @production(10)
  def pIntBVDivision$0(v0$22 : Int, v1$28 : Int): Int = v0$22 / v1$28

  @production(6)
  def pIntBVAnd$0(v0$23 : Int, v1$29 : Int): Int = v0$23 & v1$29

  @production(5)
  def pIntBVXOr$0(v0$24 : Int, v1$30 : Int): Int = v0$24 ^ v1$30

  @production(4)
  def pIntBVShiftLeft$0(v0$25 : Int, v1$31 : Int): Int = v0$25 << v1$31

  @production(3)
  def pIntBVLShiftRight$0(v0$26 : Int, v1$32 : Int): Int = v0$26 >>> v1$32

  @production(3)
  def pIntBVOr$0(v0$27 : Int, v1$33 : Int): Int = v0$27 | v1$33

  @production(2)
  def pIntBVRemainder$0(v0$28 : Int, v1$34 : Int): Int = v0$28 % v1$34

  @production(1)
  def pIntBVUMinus$0(v0$29 : Int): Int = -v0$29

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

  @production(46)
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

  @production(378)
  def pUnitUnitLiteral$0(): Unit = ()

  @production(111)
  def pUnitVariable$0(): Unit = variable[Unit]

  /* @production(55)
  def pBooleanFunctionInvocationcheck$0(v0$37 : Boolean): Boolean = check$80(v0$37) */

  /* @production(31)
  def pBooleanFunctionInvocationtrivial$0(): Boolean = trivial$80 */

}
