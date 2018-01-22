package leon.grammar

import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._

import Grammar._

object Max {

  def max3(b1: BigInt, b2: BigInt, b3: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && out >= b3 && (out == b1 || out == b2 || out == b3)
  })

  def max3Ex(b1: BigInt, b2: BigInt, b3: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => ((b1, b2, b3), res) passes {
      // base
      case (BigInt(1), BigInt(2), BigInt(3)) => BigInt(3)
      case (BigInt(-1), BigInt(42), BigInt(7)) => BigInt(42)
      case (BigInt(-100), BigInt(-101), BigInt(-102)) => BigInt(-100)
      // b1 < 0 -> b1
      case (BigInt(-101), BigInt(-100), BigInt(-102)) => BigInt(-100)
      // b2 < b1 -> b1 + 1
      case (BigInt(10), BigInt(9), BigInt(8)) => BigInt(10)
      // b2 <= b3 -> b3
      case (BigInt(100), BigInt(9), BigInt(8)) => BigInt(100)
      // b1 <= b2 -> b2
      case (BigInt(100), BigInt(9), BigInt(200)) => BigInt(200)
      // b2 <= b3 -> b3
      case (BigInt(300), BigInt(9), BigInt(200)) => BigInt(300)
      // b2 == 2 -> b3
      case (BigInt(300), BigInt(2), BigInt(200)) => BigInt(300)
      // b1 == 1 -> b3
      case (BigInt(1), BigInt(2), BigInt(-200)) => BigInt(1)
      // b2 == b1 - 1 -> b1
      case (BigInt(2), BigInt(1), BigInt(200)) => BigInt(200)
      // b1 == 2 -> b3
      case (BigInt(2), BigInt(10), BigInt(0)) => BigInt(10)
      // b3 == 0 -> b2
      case (BigInt(-5), BigInt(-10), BigInt(0)) => BigInt(0)
      // b2 == 1 -> b3
      case (BigInt(-5), BigInt(1), BigInt(0)) => BigInt(1)
      // b2 == b3 - 1 -> b3
      case (BigInt(5), BigInt(-1), BigInt(0)) => BigInt(5)
      // b3 == b1 - 1 -> b2
      case (BigInt(1), BigInt(-1), BigInt(0)) => BigInt(1)
      // b1 == 5 -> b1
      case (BigInt(5), BigInt(-1), BigInt(10)) => BigInt(10)
      // b1 == b2*b2 -> 1
      case (BigInt(1), BigInt(1), BigInt(10)) => BigInt(10)
      // b1 == b2 -> b3
      case (BigInt(1), BigInt(1), BigInt(-10)) => BigInt(1)
      // -b1 == b2 -> 1
      case (BigInt(-1), BigInt(1), BigInt(10)) => BigInt(10)

    }
  }

  def max3FullEx(b1: BigInt, b2: BigInt, b3: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => (((b1, b2, b3), res) passes {
      case (BigInt(0), BigInt(1), BigInt(0)) => BigInt(1) // Line 123
      case (BigInt(1), BigInt(0), BigInt(0)) => BigInt(1) // Line 145
      case (BigInt(1), BigInt(1), BigInt(1)) => BigInt(1) // Line 309
      case (BigInt(0), BigInt(1), BigInt(2)) => BigInt(2) // Line 1253
      case (BigInt(0), BigInt(2), BigInt(1)) => BigInt(2) // Line 4069
      case (BigInt(2), BigInt(1), BigInt(0)) => BigInt(2) // Line 6858
      case (BigInt(1), BigInt(0), BigInt(2)) => BigInt(2) // Line 10118
      case (BigInt(1), BigInt(2), BigInt(0)) => BigInt(2) // Line 14533
      case (BigInt(2), BigInt(0), BigInt(1)) => BigInt(2) // Line 17627
      case (BigInt(0), BigInt(-2), BigInt(-1)) => BigInt(0) // Line 24047
      case (BigInt(-2), BigInt(-1), BigInt(0)) => BigInt(0) // Line 35383
      case (BigInt(2), BigInt(3), BigInt(3)) => BigInt(3) // Line 58916
    })
  }

  def max4Ex(b1: BigInt, b2: BigInt, b3: BigInt, b4: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => (((b1, b2, b3, b4), res) passes {
      case (BigInt(1), BigInt(2), BigInt(3), BigInt(4)) => BigInt(4)
      case (BigInt(1), BigInt(2), BigInt(4), BigInt(3)) => BigInt(4)
      case (BigInt(1), BigInt(4), BigInt(2), BigInt(3)) => BigInt(4)
      case (BigInt(4), BigInt(1), BigInt(2), BigInt(3)) => BigInt(4)
    }) // && res >= b1 && res >= b2 && res >= b3 && res >= b4
  }

  def max3ExInt(b1: Int, b2: Int, b3: Int) = {
    ???[Int]
  } ensuring {
    res => (((b1, b2, b3), res) passes {
      case (1, 2, 3) => 3
      case (1, 3, 2) => 3
      case (3, 1, 2) => 3
    }) && res >= b1 && res >= b2 && res >= b3
  }

  def max3ExOnlyInt(b1: Int, b2: Int, b3: Int) = {
    ???[Int]
  } ensuring {
    res => (((b1, b2, b3), res) passes {
      case (1, 2, 3) => 3
      case (1, 3, 2) => 3
      case (3, 1, 2) => 3
    })
  }

  def add1Ex(b: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => (b, res) passes {
      case BigInt(3) => BigInt(4)
      case BigInt(4) => BigInt(5)
    }
  }

  def add2Ex(b1: BigInt, b2: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => ((b1, b2), res) passes {
      case (BigInt(3), BigInt(4)) => BigInt(7)
      case (BigInt(4), BigInt(7)) => BigInt(11)
    }
  }

  def funny(b1: BigInt, b2: BigInt) = {
    choose ((res: BigInt) => res >= b1 && res >= b2)
  } ensuring {
    res => ((b1, b2), res) passes {
      case (BigInt(3), BigInt(4)) => BigInt(7)
      case (BigInt(4), BigInt(7)) => BigInt(11)
    }
  }

}
