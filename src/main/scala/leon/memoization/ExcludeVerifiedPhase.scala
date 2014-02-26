/* Copyright 2009-2013 EPFL, Lausanne */

package leon.memoization

import leon._

import utils._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps.{functionCallsOf,preMap,preMapOnFunDef}
import purescala.TypeTrees._

import verification.{VerificationReport,VerificationCondition,VCKind}


object ExcludeVerifiedPhase extends LeonPhase[VerificationReport, Program] {

  // TODO: Add splitting of preconditions
  val name = "Exclude Verified VCs phase"
  val description = "Take a verification report for a program, and remove all verified VCs from it."


  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  
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
      val verifiedPostCons = vcs. filter { 
        _.kind == VCKind.Postcondition 
      }. sortWith { 
        (vc1,vc2) => vc1.getPos < vc2.getPos 
      }. groupBy { 
        _.getPos 
      }.toSeq.sortWith { (x1,x2) => x1._1 < x2._1 }
      
      // Now keep the original unverified postCons.
      val finalPostcons = postCons._2 zip verifiedPostCons collect { 
        case (pc, (_,vpc)) if vpc exists { _.value != Some(true) } => pc
      }
      
      
      /* Preconditions */

      // Function calls of funDef with preconditions, sorted by position
      val funCalls = ( funDef.body match {
        case Some(bd) => functionCallsOf(bd).toSeq.filter { _.tfd.hasPrecondition }
        case None => Seq()
      }).sortWith { (f1, f2) => f1.getPos < f2.getPos }
      
      // Verified preconditions of funDef, sorted by position
      val verifiedPrecons = vcs.filter { 
        _.kind == VCKind.Precondition 
      }.sortWith { 
        (f1,f2) => f1.getPos < f2.getPos 
      }.groupBy {
        _.getPos
      }.toSeq.sortWith { (x1,x2) => x1._1 < x2._1 }
      
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
      val (newArgs, newPrecon) : (Seq[ValDef], Option[Expr]) = if (funDef.hasPrecondition) {
        val extraArg = FreshIdentifier("__isVerified").setType(BooleanType)
        (
          funDef.params :+ new ValDef(extraArg, BooleanType), 
          Some(Or(Variable(extraArg), funDef.precondition.get))
        )
      } else (funDef.params, None)


      val toRet = funDef.copy(params=newArgs) // FIXME tparams OK
      
      toRet.precondition = newPrecon

      toRet.body = funDef.body map preMap(functionCallMap.get, true) 
      
      toRet.postcondition = finalPostcons.length match {
        case 0 => None 
        case 1 => Some( (postCons._1, finalPostcons.head) )
        case _ => Some( (postCons._1, And(finalPostcons)) )
      }

      toRet
    
    }

    val p = vRep.program
    
    val (verified, notVerified) = p.definedFunctions.partition{ fun => vRep.fvcs.isDefinedAt(fun) }
    
     
    // Pass verified functions through process function
    val readyVerified = for ( funDef <- verified ) yield {
      processFunction( funDef, vRep.fvcs.get(funDef).get )
    }
    
    // Even not verified functions have to have an argument added
    val readyNotVerified = for (funDef <- notVerified) yield {
      // If it has precondition, add extra argument into definition
      val newParams = if (funDef.hasPrecondition) {
        funDef.params :+ ValDef(FreshIdentifier("__isVerified"), BooleanType)
      } else funDef.params
      val newFunDef = funDef.copy(params = newParams)
      newFunDef.copyContentFrom(funDef)
      
      // For every function with precondition in the function body, 
      // add false as extra argument because we have not verified it
      def insertExtraArg(e : Expr) : Option[Expr] = e match {
        case FunctionInvocation(tfd,args) if tfd.fd.hasPrecondition =>
          Some(FunctionInvocation(tfd, args :+ BooleanLiteral(false)))
        case _ => None
      }
      preMapOnFunDef(insertExtraArg)(newFunDef)    
    }
    
    
    // Lastly, substitute all function calls in the new functions with the new functions
    val theMap = ((verified ++ notVerified) zip (readyVerified ++ readyNotVerified)).toMap
    
    def refreshFunInvs (e : Expr) = e match {
      case FunctionInvocation(TypedFunDef(fd,tps),args) if theMap.contains(fd) =>
        Some( FunctionInvocation(theMap.get(fd).get.typed(tps), args) )
      case _ => None 
    }
    
    val finalFuns = for (fun <- readyVerified ++ readyNotVerified) yield {
      preMapOnFunDef(refreshFunInvs)(fun)
    }
    
    // Give a copy of the original program, with the new functions
    p.duplicate.copy(modules = p.modules.map { module => module.copy(defs = 
      module.defs.filterNot { _.isInstanceOf[FunDef] } ++ finalFuns
    )})

  }


  override def run(ctx: LeonContext)(vRep: VerificationReport) : Program = {
    this.ctx = ctx
    
    ctx.reporter.info(vRep.summaryString)
    ctx.reporter.info("Removing proven formal contracts...")

    val toRet = excludeVerified(vRep)
    dbg(purescala.ScalaPrinter(toRet))
    toRet
  }


}
