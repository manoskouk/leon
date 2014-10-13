/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Definitions.TypedFunDef
import purescala.TypeTreeOps.instantiateType
import leon.utils.Simplifiers.synthesisSafeSimplifier
import WeightedBranchesCostModel.branchesCost
 
case object InlineAndSimplify extends Rule("Inline Functions and Simplify") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    
    val simplifier = synthesisSafeSimplifier(sctx.context, sctx.program) _
    
    val funInvs = functionCallsOf(p.phi) filter { _.args exists { _.isInstanceOf[CaseClass] } }
    
   
    def inlineInExpr(fi: FunctionInvocation, e : Expr) : Expr =
      replace(Map(fi -> inlineFunction(fi)), e)
    
    def exprCost(e : Expr) = branchesCost(e) + formulaSize(e)

    funInvs flatMap { fi => 
      val e = p.phi
      val newE = simplifier(inlineInExpr(fi,e))
      if (true) Some(//(exprCost(newE) <= 2 *exprCost(e)) Some(
        RuleInstantiation.immediateDecomp(
          p,
          this,
          List(p.copy(phi = newE)),
          forward,
          s"Inline ${fi.tfd.fd.id.name}@${fi.getPos} and simplify"
        )
      ) else None
    }

  }
}
