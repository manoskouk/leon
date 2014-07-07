package leon.test.memoization

// Which tests we are performing
object MemoTestOptions {

  val testSizesAndRepetitions = Seq(
    //(50,1), (75,1),
    //(100, 100),
    //(250, 50),
    //(500,30),
    //(1000,40),
    (2000,10)
  )

  val testLooseEq         = false // Loose equality
  val testMemo            = true  // Test memoization transformation (all meaningful tests)
  val testOutputValidity  = true  // Test if output file is valid (Pure)Scala
  val testWithVerify      = true  // Verify programs and only memoize unproven functions
  val testOutputs         = false // See if program outputs match + performance

  val testOriginal        = false// False to test only new, if original is too slow
  val testOriginalR       = true
  val testTrans           = true
  val testTransR          = true

  val applyTransform      = true  // Apply memo transform (false if you have outputs)
  val testInc             = true // Test incremental benchmarks
  val testBulk            = true  // Test bulk benchmarks
  val testPoly            = false
  val library             = false
  
  class HowToTest extends Enumeration
  case object Incremental extends HowToTest // e.g. insertions, one after the other
  case object Bulk        extends HowToTest // e.g. sorting, one time
}
