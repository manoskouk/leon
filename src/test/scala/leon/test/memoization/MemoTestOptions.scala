package leon.test.memoization

// Which tests we are performing
object MemoTestOptions {
  val testLooseEq         = false // Loose equality
  val testMemo            = true  // Test memoization transformation (all meaningful tests)
  val testOutputValidity  = true  // Test if output file is valid (Pure)Scala
  val testWithVerify      = false  // Verify programs and only memoize unproven functions
  val testOutputs         = false  // See if program outputs match + performance
  val testOriginalOut     = true  // False to test only new, if original is too slow
  val applyTransform      = true  // Apply memo transform (false if you have outputs)
  val testInc             = true // Test incremental benchmarks
  val testBulk            = true  // Test bulk benchmarks
  val testPoly            = false
  val library             = false
  
  class HowToTest extends Enumeration
  case object Incremental extends HowToTest // e.g. insertions, one after the other
  case object Bulk        extends HowToTest // e.g. sorting, one time
}
