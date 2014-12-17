/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._

class DefaultEvaluator(ctx: LeonContext, prog: Program, cacheFunctionCalls: Boolean = false) extends RecursiveEvaluator(ctx, prog, 50000, cacheFunctionCalls) {
  type RC = DefaultRecContext
  type GC = GlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = new GlobalContext()

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }
}
