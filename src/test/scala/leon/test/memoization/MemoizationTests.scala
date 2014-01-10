/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package memoization

import leon._
import leon.purescala.PrettyPrinter
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.purescala.Common._
import memoization._

import leon.evaluators._
import leon.evaluators.CodeGenEvaluator._
import leon.evaluators.EvaluationResults._
import leon.codegen.CodeGenParams

import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}


class MemoizationSuite extends LeonTestSuite {
  
  // Which tests we are performing
  val testLooseEq = false 
  val testMemo    = true
 
  // Define expressions which define CaseClass expression equality correctly
  def looseTypeEq(t1 : TypeTree, t2: TypeTree) : Boolean = (t1, t2) match {
    case (AnyType, AnyType) | (BottomType, BottomType) | (BooleanType, BooleanType) | 
         (Int32Type, Int32Type) | (UnitType, UnitType) => true
    case (TupleType(tps1), TupleType(tps2)) => 
      tps1.length == tps2.length &&
      (tps1 zip tps2 forall { case (tp1, tp2) => looseTypeEq(tp1, tp2) })
    case (ListType(base1)     , ListType(base2)    ) => looseTypeEq(base1, base2)
    case (SetType(base1)      , SetType(base2)     ) => looseTypeEq(base1, base2)
    case (MultisetType(base1) , MultisetType(base2)) => looseTypeEq(base1, base2)
    case (MapType(from1, to1) , MapType(from2, to2)) => 
      looseTypeEq(from1, from2) && looseTypeEq(to1, to2)
    case (FunctionType(from1, to1), FunctionType(from2, to2)) => 
      from1.size == from2.size && 
      ( from1 zip from2 forall { case (fr1,fr2) => looseTypeEq(fr1,fr2) } ) &&
      looseTypeEq(to1, to2)
    case (ArrayType(base1)    , ArrayType(base2) )  => looseTypeEq(base1, base2)
    case (AbstractClassType(c1), AbstractClassType(c2)) => c1.id.name == c2.id.name
    case (CaseClassType(c1),     CaseClassType(c2)) => c1.id.name == c2.id.name
    case _ => false 
  }


  // equality on data structures according to name only, 
  // so as to compare structures from input and output programs
  // currently only compares constants
  // handles large test cases, so uses side effects
  def looseEq(e1: Expr, e2: Expr) : Boolean = {
    import scala.collection.mutable._
    val q = new Queue[(Expr,Expr)]()

    def localEq(e1:Expr, e2:Expr) : Boolean = (e1, e2) match { 
      case ( IntLiteral(i1), IntLiteral(i2) ) => 
        i1 == i2 
      case ( StringLiteral(s1), StringLiteral(s2) ) => 
        s1 == s2
      case ( BooleanLiteral(b1), BooleanLiteral(b2) ) =>  
        b1 == b2
      case ( UnitLiteral, UnitLiteral ) => 
        true
      case ( FiniteArray(exs1), FiniteArray(exs2) ) =>
        if (exs1.length != exs2.length) false 
        else { 
          exs1 zip exs2 foreach { q += _ } 
          true
        }
      case ( NilList(t1), NilList(t2) ) => 
        looseTypeEq(t1,t2)
      case ( Cons(h1, t1) , Cons(h2,t2) ) => {
        q += ((h1,h2),(t1,t2))
        true
      }
      case ( Tuple(exs1), Tuple(exs2) ) =>  
        if (exs1.length != exs2.length) false 
        else { 
          exs1 zip exs2 foreach { q += _ } ;
          true
        }
      case ( Error(_), Error(_)) => 
        true      
      case ( CaseClass(c1, args1), CaseClass(c2, args2) ) => 
        
        if (c1.id.name == c2.id.name) { 
          val l = scala.math.min(args1.length, args2.length)
          val originalFields = args1.take(l) zip args2.take(l)
          originalFields foreach { q += _ }
          true
        }
        else false  
      
      
      // FIXME : Hope that sets return items in the same order too...
      case ( f1@FiniteMap(pairs1), f2@FiniteMap(pairs2) ) => 
        if(pairs1.isEmpty && pairs2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else {
          if ( pairs1.size == pairs2.size ) { 
            pairs1 zip pairs2 foreach { case ((from1,to1), (from2,to2)) => 
              q.enqueue( (from1, from2), (to1,to2) )
            }
            true
          }
          else false 
        }

      case ( f1@FiniteSet(els1), f2@FiniteSet(els2) ) => 
        if(els1.isEmpty && els2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else { 
          if ( els1.size == els2.size ) { 
            els1 zip els2 foreach { q += _ }
            true
          } 
          else false 
        }

      case ( f1@FiniteMultiset(els1), f2@FiniteMultiset(els2) ) => 
        if(els1.isEmpty && els2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else {
          if ( els1.size == els2.size ) { 
            els1 zip els2 foreach { q += _ }
            true
          } 
          else false 
        }
      case ( EmptyMultiset(t1), EmptyMultiset(t2) ) => 
        looseTypeEq(t1,t2)


      /*
      case ( Choose(vars1, pred1), Choose(vars2, preds2) ) => true // FIXME
      case ( Let(bind1, val1, bd1), Let(bind2, val2, bd2) ) => true
      case ( LetTuple(bind1, val1, bd1), LetTuple(bind2, val2, bd2) ) => true
      case ( LetDef(fd1, bd1), LetDef(fd2,bd2) ) => true
      case ( FunctionInvocation(f1, args1), FunctionInvocation(f2, args2)) => true
      case ( IfExpr(cond1, thenn1, elze1), IfExpr(cond1, thenn1, elze1)) =>
      case ( TupleSelect(tpl1, index1), TupleSelect(tpl1, index1) ) => true
      case ( MatchExpr(scr1, cases1), MatchExpr(scr2, cases2) ) => true
      case ( And(exprs1), And(exprs2) ) => 
      case ( Or(exprs1), Or(exprs2) ) => 
      case ( Iff(l1, r1), Iff(l2, r2) ) => 
      case ( Implies(l1, r1), Implies(l2, r2) ) => 
      case ( Not(
      */
      case _ => false 
    }       
    
    
    q += ((e1,e2))
    while (!q.isEmpty) {
      val (e1,e2) = q.dequeue()
      if (!localEq(e1,e2)) return false
    }
    return true

  }

  // Time a block and return time in microseconds
  def time[A]( block : => A) : (A, Long) = {
    val before = System.nanoTime
    val res    = block
    val after  = System.nanoTime 
    (block, (after - before)/1000)
  }

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }

  val pipeFront = frontends.scalac.ExtractionPhase andThen utils.SubtypingPhase 
  val inputFilePath  = "regression/memoization/original"
  val outputFilePath = "regression/memoization/memoOut"
  val testFilePath   = "regression/memoization/tests"

  //val testSizes = Seq(10,1000, 2500, 10000, 20000)
  val testSizes = Seq(100, 1000, 2000)

  private def testMemo(f : File) { 
    val outFile  = new File ( 
      resourceDir(outputFilePath).getAbsolutePath ++ "/" ++ f.getName 
    )
    val testFile = new File ( 
      resourceDir(testFilePath  ).getAbsolutePath ++ "/" ++ 
      (f.getName.substring(0,f.getName.length - 6)) + "Tests.scala" 
    )

    test ("Testing " + f.getName) {
      // Compile original file
      val ctx = testContext.copy(
        // We want a reporter that actually prints some output
        reporter = new DefaultReporter(testContext.settings)
      )

      ctx.reporter.info("Transforming " + f.getAbsolutePath)
      val transAST = { 
        import verification.VerificationReport
        val interm = new LeonPhase[Program,VerificationReport] { 
          val description = ""
          val name = ""
          def run(ctx : LeonContext)(p : Program ) : VerificationReport = 
            VerificationReport.emptyReport(p)
        } 
        (pipeFront andThen interm andThen MemoizationPhase).run(
          ctx.copy(settings = Settings(memo =  outFile.getAbsolutePath))
        )(f.getAbsolutePath :: Nil)
      }
      
      ctx.reporter.info("Recompiling original " + f.getName)
      
      val origAST = pipeFront.run(ctx)(f.getAbsolutePath :: Nil) 
      
      //this is not ideal, but the normal way has bugs  :(
      //ctx.reporter.info( "Recompiling transformed")

      //val transAST2 = pipeFront.run(ctx)(outFile.getAbsolutePath :: Nil) 
      val transAST2 = transAST
      
      def compileTestFun(p : Program) : (Expr, (Expr, Int) => EvaluationResults.Result) = { 
        //ctx.reporter.info(PrettyPrinter(p))
        //ctx.reporter.info("Defined functions: " + (p.definedFunctions filter { _.hasImplementation } map (_.id.name) mkString(", ")))
        // We want to produce code that checks contracts
        val evaluator = new CodeGenEvaluator(ctx, p , CodeGenParams(checkContracts = true))
        val testFun =  p.definedFunctions.find(_.id.name == "test").getOrElse {
          ctx.reporter.fatalError("Test function not defined!")
        }
        val initVal = p.definedFunctions.find(_.id.name == "init").getOrElse {
          ctx.reporter.fatalError("Initial value not defined!")
        }.body.get

        val args = testFun.args map { _.id }
        val body = testFun.body.get

        (initVal, evaluator.compileRec(body, args).getOrElse{ctx.reporter.fatalError("Failed to compile test function!")})
      }


      ctx.reporter.info("Compiling original to bytecode")
      val (init1, compiled1) = compileTestFun(origAST)
      ctx.reporter.info("Compiling transformed to bytecode")
      // Cheating around bug
      // val ex2 = compileAndTest(transAST)
      val (init2, compiled2) = compileTestFun(transAST2)
      
      for (size <- testSizes) { 
        ctx.reporter.info("Now testing for input size " + size)
        val (res1, time1) = time{compiled1(init1,size)}
        val (res2, time2) = time{compiled2(init2,size)} 
        (res1, res2) match {
          case (Successful(ex1), Successful(ex2)) if (looseEq(ex1,ex2)) => {
            ctx.reporter.info("  Both programs produced the same output!")
            ctx.reporter.info("  Time for original    : " + time1 + " microsec.")
            ctx.reporter.info("  Time for transformed : " + time2 + " microsec.")
          } 
          case (RuntimeError(mess1), RuntimeError(mess2)) => 
            ctx.reporter.info("  Both programs produced an error") 
          case (EvaluatorError(mess1), _ ) => 
            ctx.reporter.fatalError ("  Evaluation failed with message: " + mess1)
          case (_, EvaluatorError(mess2) ) => 
            ctx.reporter.fatalError ("  Evaluation failed with message: " + mess2)
          case _ => 
            ctx.reporter.error("Error")
            ctx.reporter.error("  Result1 = \n" + res1.toString)
            ctx.reporter.error("  Result2 = \n" + res2.toString)
            ctx.reporter.fatalError("  Outputs don't match for input size " + size) 
        }
      }

    }

  }

  // looseEq tests
  if (testLooseEq) {  
    
    val theTests = Seq(
      (
        IntLiteral(0), 
        IntLiteral(0),
        true
      ),
      (
        IntLiteral(0), 
        IntLiteral(1),
        false
      ), 
      (
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(IntLiteral(1), IntLiteral(2), BooleanLiteral(true))
        ),
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(IntLiteral(1), IntLiteral(2), BooleanLiteral(true))
        ),
        true
      ),
      (
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(IntLiteral(0), IntLiteral(2), BooleanLiteral(true))
        ),
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(IntLiteral(1), IntLiteral(2), BooleanLiteral(true))
        ),
        false
      ),
      (
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(
            IntLiteral(1), 
            IntLiteral(2), 
            BooleanLiteral(true), 
            CaseClass(new CaseClassDef(FreshIdentifier("None")), Seq()),
            IntLiteral(42)
          )
        ),
        CaseClass(
          new CaseClassDef(FreshIdentifier("Hello")), 
          Seq(
            IntLiteral(1), 
            IntLiteral(2), 
            BooleanLiteral(true)
          )
        ),
        true
      )

      

    )


    for( ((ex1, ex2, expected), index) <- theTests.zipWithIndex) {
      test("Testing looseEq " + index) {
        assert(looseEq(ex1,ex2) == expected)
      }
    }


  }

  // Actual memoization tests
  if (testMemo) {
    forEachFileIn(inputFilePath) { f => 
      testMemo(f)
    }
  }

  
}
