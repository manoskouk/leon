/* Copyright 2009-2013 EPFL, Lausanne */

package leon.memoization

import leon._

import utils._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.DefOps.{applyOnFunDef,preMapOnFunDef}
import purescala.TypeTrees._
import purescala.TypeTreeOps.{typeParamSubst,instantiateType}

import verification.{VerificationReport,VerificationCondition}


object MemoizationPhase extends TransformationPhase {

  val name = "Memoization transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep Memoization information"
  override val definedOptions : Set[LeonOptionDef] = Set( 
    LeonFlagOptionDef("no-verify", "--no-verify", "Skip verification before memoization transformation.")
  )

  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  
  private def acceptableParams(f : FunDef) = {
    f.params.size == 1 ||
    f.params.size == 2 && f.params.tail.head.id.name == "__isVerified"
  }
  
  // Identifier printing strategy. true is mostly for debugging
  private val alwaysShowUniqueId = false 
  // Take an Identifier and produce a fresh with lowewcase first letter
  private def idToFreshLowerCase(id : Identifier) = {
    assert(!id.name.isEmpty)
    FreshIdentifier(nameToLowerCase(id.name), id.getType, alwaysShowUniqueId)
  }
  
  private def nameToLowerCase(name : String ) = {
    assert(!name.isEmpty)
    name.updated(0, name(0).toLower)
  }


  // Find which functions (may) need to get memoized
  private def findCandidateFuns(p: Program) : Set[FunDef]= {
    
    // All unproven VCs that we receive from the previous pipeline phases
    val unprovenVCs = p.definedFunctions flatMap {
      fn => fn.precondition.toSeq ++ fn.postcondition.toSeq
    }
    dbg("I have these conditions")
    dbg( unprovenVCs map { con => 
      con.toString + "@" + con.getPos.toString 
    } mkString ("\n") )
    
    
    val referredFuns : Set[FunDef] = for (
      cond : Expr <- unprovenVCs.toSet;
      fi   <- functionCallsOf(cond)
    ) yield fi.tfd.fd
    dbg("Referred functions:\n" + referredFuns.map{_.id.name}.mkString("\n"))
    
    val transCalles = referredFuns flatMap p.callGraph.transitiveCallees
    dbg("Transitive callees:\n" + transCalles.map{_.id.name}.mkString("\n"))

    // The trans. closure of functions that are called from VCs 
    val allCandidates = transCalles ++ referredFuns ++  
      // ... and add the functions the user has annotated with forceMemo
      (p.definedFunctions filter { _.annotations.contains("forceMemo") } ).toSet
    dbg("I found these candidates:\n" + allCandidates.map {_.id.name}.mkString("\n"))
    
    // Filter these to have the desired form
    val recMemo = allCandidates filter { f =>  
      acceptableParams(f) &&
      f.params.head.getType.isInstanceOf[ClassType] &&
      p.callGraph.transitivelyCalls(f,f) &&
      ( 
        // TODO : clear out what happens in these cases.   
        if (f.returnType.isInstanceOf[ClassType]) { 
          val rootRet   = f.returnType.         asInstanceOf[ClassType].classDef.hierarchyRoot 
          val rootParam = f.params.head.getType.asInstanceOf[ClassType].classDef.hierarchyRoot 
          rootRet != rootParam
        }
        else true 
      )
    }
    
    // Every function that transitively calls a recursive function NOT in this list should be dropped
    val recNotMemo = p.definedFunctions.filter{ p.callGraph.isRecursive(_) }.toSet -- recMemo.toSet
    val toRet = recMemo -- p.callGraph.transitiveCallers(recNotMemo)
    
    for (fun <- recMemo -- toRet) {
      ctx.reporter.info(s"${fun.id.name} is not considered for memoization, as it is calling a non-memoized recursive function")
    }
    
    dbg("I found these final candidates:\n" + toRet.map {_.id.name}.mkString("\n"))
    
    toRet 
  }

  
  def apply(ctx: LeonContext, p : Program) : Program  = {

    this.ctx = ctx

   
    ctx.reporter.info(s"Applying memoization transformation on ${p.id}")
    
    val candidateFuns = findCandidateFuns(p) 
    val newFuns = candidateFuns map { fn =>
      import fn._
      val toRet = new FunDef(
        id,
        tparams,
        returnType,
        params.take(1), // If we have decided to memoize this function,
                        // we want it to have only the receiver as argument.
                        // So we kick out the __isVerified parameter  
        DefType.StrictFieldDef
      ).copiedFrom(fn)
      toRet.copyContentFrom(fn)
      toRet.precondition = precondition match {
        case Some(Or(Seq(Variable(id), prec))) if id.name == "__isVerified" => Some(prec)
        case other => other
      }
      toRet
    }

    val f2f = candidateFuns.zip(newFuns).toMap
    
    val newProg = new Program(p.id, p.units.map{ u => u.copy(modules = u.modules map { mod =>
      mod.copy(defs = mod.defs map { _ match {  
        case fn : FunDef => 
          preMapOnFunDef{
            case FunctionInvocation(TypedFunDef(fd,tps),args) if f2f.contains(fd) =>
              Some(FunctionInvocation(f2f(fd).typed(tps), args.take(1))) // Don't keep __isVerified in function calls
            case _ => None 
          }(f2f.get(fn).getOrElse(fn))
        case other => other
      }})
    })})
    newProg

  }


}

