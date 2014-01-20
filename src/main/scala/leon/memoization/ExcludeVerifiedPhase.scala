package leon
package memoization

import leon._
import leon.utils._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Trees._
import purescala.Common._
import verification.VerificationReport
import verification.VerificationCondition
import verification.VCKind

object ExcludeVerifiedPhase extends LeonPhase[VerificationReport, Program] {

  // TODO: make this phase filter preconditions too
  val name = "Exclude Verified VCs phase"
  val description = "Take a verification report for a program, and remove all verified VCs from it."


  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  
  // TODO only works for postconditions
  def excludeVerified(vRep : VerificationReport) : Program = {
    
    def processFunction(funDef : FunDef, vcs : Seq[VerificationCondition]) : FunDef = {

      /* Postconditions */
      val postCon = funDef.postcondition
      // Separate postconditions
      val postCons : (Identifier, Seq[Expr]) = postCon match {
        case Some( (id, And(args)) ) => (id, args.sortWith{ (e1,e2) => e1.getPos < e2.getPos })
        case Some( (id, cond     ) ) => (id, Seq(cond))
        case None                    => (FreshIdentifier("_"), Seq())
      }

      // Get the postcondition VCs, make sure they are in the right order.
      // Because InductionTactic may generate multiple conditions from one expr. we have to group them
      val verifiedPostCons = ( vcs filter { 
        _.kind == VCKind.Postcondition 
      } sortWith { 
        (vc1,vc2) => vc1.getPos < vc2.getPos 
      } groupBy { 
        _.getPos 
      }).toSeq
      
      // Now keep the original unverified postCons.
      val finalPostcons = postCons._2 zip verifiedPostCons collect { 
        case (pc, vpc) if vpc._2 exists { _.value != Some(true) } => pc
      }
      
      
      /* Preconditions */

      // Function calls of funDef with preconditions, sorted by position
      val funCalls = functionCallsOf(funDef.body.get).toSeq.filter { _.funDef.hasPrecondition }.
        sortWith { (f1, f2) => f1.getPos < f2.getPos }
      // Verified rreconditions of funDef, sorted by position
      val verifiedPrecons = ( vcs filter { 
        _.kind == VCKind.Precondition 
      } sortWith { 
        (f1,f2) => f1.getPos < f2.getPos 
      } groupBy {
        _.getPos
      }).toSeq
      
      // To function invocations with preconditions, add an extra argument saying if it is verified or not
      val functionCallMap : Map[Expr, Expr] = ( 
        for ( (fi@FunctionInvocation(funDef,args), pc) <- funCalls zip verifiedPrecons ) yield {
          ( fi, FunctionInvocation(
            funDef, 
            args :+ BooleanLiteral( pc._2 forall { _.value == Some(true)} )
          ))
        }
      ).toMap

      // To the function definition itself, add an extra argument if it has precon.
      // that says if it has been verified.
      val (newArgs, newPrecon) : (VarDecls, Option[Expr]) = if (funDef.hasPrecondition) {
        val extraArg = FreshIdentifier("__isVerified").setType(BooleanType)
        (
          funDef.args :+ new VarDecl(extraArg, BooleanType), 
          Some(Or(Variable(extraArg), funDef.precondition.get))
        )
      } else (funDef.args, None)


      val toRet = new FunDef(funDef.id, funDef.returnType, newArgs)
      
      toRet.precondition = newPrecon

      toRet.body = Some(searchAndReplace(functionCallMap.get)(funDef.body.get) )
      
      toRet.postcondition = finalPostcons.length match {
        case 0 => None 
        case 1 => Some( (postCons._1, finalPostcons.head) )
        case _ => Some( (postCons._1, And(finalPostcons)) )
      }

      toRet
    
    }

    val p = vRep.program
    // Process all functions of p, with no VCs for unverified functions
    val definedFunctions = for ( funDef <- p.definedFunctions ) yield {
      processFunction( funDef, vRep.fvcs.getOrElse(funDef,Seq()) )
    }
    // Give a copy of the original program, with the new functions
    p.duplicate.copy(mainObject = p.mainObject.copy(defs = 
      p.mainObject.defs.filterNot { _.isInstanceOf[FunDef] } ++ definedFunctions
    ))


  }


  override def run(ctx: LeonContext)(vRep: VerificationReport) : Program = {
    this.ctx = ctx
    dbg(vRep.summaryString)
    excludeVerified(vRep)
  }


}
