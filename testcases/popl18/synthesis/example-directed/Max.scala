import leon.annotation._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Max {

  def max2(i1: BigInt, i2: BigInt): BigInt = {
    ???[BigInt]
  } ensuring { res =>
    ((i1, i2), res) passes {
      case (BigInt(10), BigInt(-88)) => BigInt(10)
      case (BigInt(0), BigInt(1)) => BigInt(1)
    }
  }

  def max3(i1: BigInt, i2: BigInt, i3: BigInt): BigInt = {
    ???[BigInt]
  } ensuring { res =>
    ((i1, i2, i3), res) passes {
      case (BigInt(10), BigInt(-88), BigInt(3)) => BigInt(10)
      case (BigInt(0), BigInt(1), BigInt(-99)) => BigInt(1)
      case (BigInt(-42), BigInt(-99), BigInt(42)) => BigInt(42)
    }
  }
}
