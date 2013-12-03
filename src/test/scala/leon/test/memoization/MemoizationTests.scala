/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package memoization

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import memoization._

/*import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._
*/
import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}


class MemoizationSuite extends LeonTestSuite {
  
  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }

  val pipeline = frontends.scalac.ExtractionPhase andThen utils.SubtypingPhase andThen MemoizationPhase
  val inputFilePath = "regression/memoization/original"
  val outputFilePath = "regression/memoization/memoOut"
  
  private def testMemo(f : File) { test ("Testing " + f.getName) {
    val ctx = testContext.copy(settings = Settings(
      memo = resourceDir(outputFilePath).getAbsolutePath ++ "/" ++ f.getName
    ))

    println(ctx.settings.memo)
    val ast = pipeline.run(ctx)(f.getAbsolutePath :: Nil)
    
    
  }}


  forEachFileIn(inputFilePath) { f => 
    testMemo(f)
  }


  
}
