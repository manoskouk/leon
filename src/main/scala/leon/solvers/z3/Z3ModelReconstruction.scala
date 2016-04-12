/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers.z3

import com.microsoft.z3._

import purescala.Common._
import purescala.Expressions.{ Expr => LeonExpr, _}
import purescala.ExprOps._
import purescala.Types._

trait Z3ModelReconstruction {
  self: AbstractZ3Solver =>

  // exprToZ3Id, softFromZ3Formula, reporter

  private final val AUTOCOMPLETEMODELS : Boolean = true

  def modelValue(model: Model, id: Identifier, tpe: TypeTree = null) : Option[LeonExpr] = {
    val expectedType = if(tpe == null) id.getType else tpe

    variables.getB(id.toVariable).flatMap { z3ID =>
      softFromZ3Formula(model, model.eval(z3ID, true), expectedType) // FIXME ???
    }
  }

  def modelToMap(model: Model, ids: Iterable[Identifier]) : Map[Identifier, LeonExpr] = {
    var asMap = Map.empty[Identifier, LeonExpr]

    def completeID(id : Identifier) : Unit = {
      asMap = asMap + (id -> simplestValue(id.getType))
      reporter.debug("Completing variable '" + id + "' to simplest value")
    }

    for (id <- ids) {
      modelValue(model, id) match {
        case None if AUTOCOMPLETEMODELS => completeID(id)
        case None => ;
        case Some(v @ Variable(exprId)) if AUTOCOMPLETEMODELS && exprId == id => completeID(id)
        case Some(ex) => asMap = asMap + (id -> ex)
      }
    }

    asMap
  }

  def printExtractedModel(model: Model, ids : Iterable[Identifier]) : Unit = {
    reporter.info("Tentative extracted model")
    reporter.info("*************************")
    for(id <- ids) {
      val strRep = modelValue(model, id) match {
        case Some(e) => e.toString
        case None => "??"
      }
      reporter.info(id + "       ->     " + strRep)
    }
  }
}
