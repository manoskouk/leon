/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Constructors._
import purescala.Expressions.Expr
import purescala.Extractors.IsTyped
import purescala.Types._

case class BooleanGrammar(inputs: Seq[Expr]) extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = t match {
    case BooleanType =>
      for {
        IsTyped(in, act: AbstractClassType) <- inputs
        cct <- act.knownCCDescendants
      } yield {
        terminal(isInstOf(in, cct))
      }
    case _ =>
      Nil
  }
}