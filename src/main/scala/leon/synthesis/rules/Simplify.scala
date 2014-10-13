/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import leon.utils.Simplifiers.synthesisSafeSimplifier

case object Simplify extends NormalizingRule("Simplification") {
  override val priority = RulePriorityNormalizing

  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val simplifier =  synthesisSafeSimplifier(sctx.context, sctx.program) _
    val sPhi = simplifier(p.phi)
    val sPc  = simplifier(p.pc)
    if ( sPhi == p.phi && sPc == p.pc)
      None
    else {
      val sub = Problem(p.as, sPc, sPhi, p.xs)
      Some(RuleInstantiation.immediateDecomp(p,this, List(sub), forward, s"Simplify into $sub"))
    }
  }
}
