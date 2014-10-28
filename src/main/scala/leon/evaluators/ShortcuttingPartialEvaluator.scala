/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala._
import Definitions.Program
import Trees.Expr

class ShortcuttingPartialEvaluator(context: LeonContext, program : Program) extends PartialEvaluator(context, program) {

  override val name = "partial evaluator, shortcuts around errors"
  override val description = "Partial evaluator for PureScala programs. Does NOT respect Error semantics. Does not attempt to unfold recursive functions."

  override protected val errorFree = (e : Expr) => true 

}
