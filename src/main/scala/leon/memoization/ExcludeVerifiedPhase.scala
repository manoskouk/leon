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

  val name = "Exclude Verified VCs phase"
  val description = "Take a verification report for a program, and remove all verified VCs from it."


  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  
  // TODO only works for postconditions
  def excludeVerified(vRep : VerificationReport) : Program = {
    
    def processFunction(funDef : FunDef, vcs : Seq[VerificationCondition]) : FunDef = {
      val postCon = funDef.postcondition
      // Separate postconditions
      val postCons : (Identifier, Seq[Expr]) = postCon match {
        case Some( (id, And(args)) ) => (id, args)
        case Some( (id, cond     ) ) => (id, Seq(cond))
        case None                    => (FreshIdentifier("_"), Seq())
      }

      val verifiedPostCons = vcs filter { _.kind == VCKind.Postcondition } 
      
      // Now keep the original unverified postCons.
      val toKeep = (postCons._2 zip verifiedPostCons) collect { 
        case (pc, vpc) if vpc.value != Some(true) => pc
      }
      
      val toRet = funDef.duplicate
      toRet.postcondition = toKeep.length match {
        case 0 => None 
        case 1 => Some( (postCons._1, toKeep.head) )
        case 2 => Some( (postCons._1, And(toKeep)) )
      }

      toRet
    
    }

    val vcMap = vRep.fvcs
    val p = vRep.program
    // For each function that got verified, exclude verified postcond.
    val withExcludedVCs = for (vc <- vcMap.toSeq) yield {
      processFunction(vc._1, vc._2)
    }

    // Add to these the unverified functions
    val definedFunctions = (
      p.definedFunctions.toSet -- ( 
        vcMap.toSet.map { x : (FunDef, Seq[VerificationCondition]) => x._1 } 
      )
    ).toSeq ++ withExcludedVCs

    // Give a copy of the original program, with the new functions
    vRep.program.duplicate.copy(mainObject = p.mainObject.copy(defs = 
      p.mainObject.defs.filterNot { _.isInstanceOf[FunDef] } ++ definedFunctions
    ))


  }

/*
  // Find which functions (may) need to get memoized
  def findCandidateFuns(vRep : VerificationReport) : Set[FunDef]= {
    val p = vRep.program
    val referredFuns : Set[FunDef] = if (vRep.fvcs.isEmpty) {
      dbg("EMPTY REPORT")
      p.definedFunctions.toSet 
    } else {
      // Find all functions that are referred to from unproven conditions
      val convert: Expr => Set[FunDef] = (_ => Set.empty)
      val combine: (Set[FunDef],Set[FunDef]) => Set[FunDef] = (s1, s2) => s1 ++ s2
      def compute(e: Expr, funs: Set[FunDef]) :  Set[FunDef] = e match {
        case FunctionInvocation(f2, _) => funs + f2
        case _ => funs
      }

      dbg("I have these unproven conditions\n" + vRep.conditions.filter { _.value!= Some(true) }. map {_.condition}.mkString("\n"))
      val funSets = vRep.conditions filter { 
        _.value != Some(true) 
      } map { 
        cond:VerificationCondition => treeCatamorphism(convert, combine, compute, cond.condition) 
      }
      dbg("Referred functions:\n " + funSets.toSet.flatten.map{_.id.name}.mkString("\n"))
      val toRet1 = funSets.toSet.flatten flatMap p.transitiveCallees

      dbg("Transitive callees:\n " + toRet1.map{_.id.name}.mkString("\n"))
      // The trans. closure of functions that are called from VCs 
      val toRet = (toRet1) ++ funSets.toSet.flatten ++ 
      // ... and add the functions the user has annotated with forceMemo
      (p.definedFunctions filter { fun => fun.annotations.contains("forceMemo") } ).toSet
      dbg("I found these candidates:\n" + toRet.map {_.id.name}.mkString("\n"))
      toRet
    
    }

    // Filter these to have the desired form
    val toRet = referredFuns filter { f =>  
      f.args.size == 1 &&
      f.args.head.getType.isInstanceOf[ClassType] &&
      p.transitivelyCalls(f,f) 
    }

    dbg("I found these final candidates:\n" + toRet.map {_.id.name}.mkString("\n"))
    toRet 
  }
  */
  override def run(ctx: LeonContext)(vRep: VerificationReport) : Program = {
    this.ctx = ctx
    dbg(vRep.summaryString)
    excludeVerified(vRep)
  }


}
