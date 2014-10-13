/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Definitions.TypedFunDef
import purescala.TypeTreeOps.instantiateType
 
case object InlineFunctions extends Rule("Inline Functions") {

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    
    val funInvs = functionCallsOf(p.phi)
    
    def inlineInExpr(fi: FunctionInvocation, e : Expr) : Expr =
      replace(Map(fi -> inlineFunction(fi)), e)

    funInvs map { fi =>
      RuleInstantiation.immediateDecomp( 
        p, 
        this, 
        List(p.copy(phi = matchToIfThenElse(inlineInExpr(fi, p.phi)))),
        forward, 
        s"Inline ${fi.tfd.fd.id.name} @ ${fi.getPos}"
      )
    }

  }
}
