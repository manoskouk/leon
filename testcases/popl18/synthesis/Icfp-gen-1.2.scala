package leon
package grammar

import leon.lang._
import leon.annotation.grammar._
import leon.lang.synthesis._
import annotation.grammar._

object IC {
  @production(1) def shr1(x: Int) = x >> 1
  @production(1) def shr4(x: Int) = x >> 3
  @production(1) def shr16(x: Int) = x >> 16
  @production(1) def bvand(x: Int, y: Int) = x & y
  @production(1) def bvor(x: Int, y: Int) = x | y
  @production(1) def bxvor(x: Int, y: Int) = x ^ y
  @production(1) def bvadd(x: Int, y: Int) = x + y
  @production(1) def if1(x: Int, y: Int, z: Int) = if (x == 1) y else z
  @production(1) def vbv = variable[Int]
  @production(1) def bvnot(x: Int) = ~x

  def f(i: Int): Int = {
    ???[Int]
  } ensuring { res =>
    (i, res) passes {
      case 2173683 => 1231288
      case 2190383 => 1902393
    }
  }
}

