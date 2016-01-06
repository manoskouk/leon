/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Definitions._
import purescala.Types._
import purescala.TypeOps._

import synthesis.{SynthesisContext, Problem}

object Grammars {

  def default(prog: Program, inputs: Seq[Expr], currentFunction: FunDef, exclude: Set[FunDef], ws: Expr, pc: Expr): ExpressionGrammar[TypeTree] = {
    BaseGrammar ||
    EqualityGrammar(Set(IntegerType, Int32Type, BooleanType) ++ inputs.map { _.getType }) ||
    OneOf(inputs) ||
    BooleanGrammar(inputs) ||
    FunctionCalls(prog, currentFunction, inputs.map(_.getType), exclude) ||
    SafeRecursiveCalls(prog, ws, pc)
  }

  def default(sctx: SynthesisContext, p: Problem): ExpressionGrammar[TypeTree] = {
    default(sctx.program, p.as.map(_.toVariable), sctx.functionContext, sctx.settings.functionsToIgnore,  p.ws, p.pc)
  }

  def typeDepthBound[T <% Typed](g: ExpressionGrammar[T], b: Int) = {
    g.filter(g => g.subTrees.forall(t => typeDepth(t.getType) <= b))
  }
}
