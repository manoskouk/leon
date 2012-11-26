package leon
package solvers.z3

import z3.scala._

import leon.solvers.Solver

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
class UninterpretedZ3Solver(context : LeonContext) extends Solver(context) with AbstractZ3Solver with Z3ModelReconstruction {
  val description = "Uninterpreted Z3 Solver"
  override val shortDescription = "Z3-u"

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "MBQI" -> false,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  protected[leon] def prepareFunctions : Unit = {
    functionMap        = Map.empty
    reverseFunctionMap = Map.empty
    for(funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = functionMap(funDef)
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef = reverseFunctionMap(decl)
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)

  override def solve(expression: Expr) : Option[Boolean] = solveSAT(Not(expression))._1.map(!_)

  // Where the solving occurs
  override def solveSAT(expression : Expr) : (Option[Boolean],Map[Identifier,Expr]) = {
    restartZ3

    val emptyModel    = Map.empty[Identifier,Expr]
    val unknownResult = (None, emptyModel)
    val unsatResult   = (Some(false), emptyModel)

    val result = toZ3Formula(expression).map { asZ3 => 
      z3.assertCnstr(asZ3)
      z3.checkAndGetModel() match {
        case (Some(false), _) => unsatResult
        case (Some(true), model) => {
          if(containsFunctionCalls(expression)) {
            unknownResult
          } else { 
            val variables = variablesOf(expression)
            val r = (Some(true), modelToMap(model, variables))
            model.delete
            r
          }
        }
        case _ => unknownResult
      }
    } getOrElse unknownResult

    result
  }
}
