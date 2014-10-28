/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala._

import Definitions._
import TreeOps._
import Common._
import TypeTrees._
import Trees._
import TypeTreeOps._
import Extractors._
import EvaluationResults._


class PartialEvaluator(context: LeonContext, program : Program) extends Evaluator(context, program) {

  val name = "partial evaluator"
  val description = "Partial evaluator for PureScala programs. Respects Error semantics. Does not attempt to unfold recursive functions."

  // All functions whose evaluation could (transitively) result in an error
  private val erroneousFuns : Set[FunDef] = {
    def isErroneous(fd : FunDef) = exists { 
      case _ : Error | _ : Assert | _ : Require | _ : Ensuring => true
      case _ => false 
    }(fd.fullBody)

    program.definedFunctions.toSet filter { fd =>
      (program.callGraph.transitiveCallees(fd) + fd) exists isErroneous
    }
  }

  // Returns true if the evaluation of 'e' may potentially result in an Error
  protected val errorFree = (e : Expr) => !exists{
    case _ : Error | _ : Assert | _ : Require | _ : Ensuring => true
    case fi : FunctionInvocation if erroneousFuns contains fi.tfd.fd => true
    case mi : MethodInvocation   if erroneousFuns contains mi.tfd.fd => true
    case _ => false 
  }(e)
  private val isFullyEvaluated = (e : Expr) => errorFree(e) && isGround(e)

  private def keys( fm : FiniteMap) = {
    val (keys, _) = fm.singletons.unzip
    keys
  }

  // Does not unfold any function definitions
  def oneStep(mapping : Map[Identifier, Expr])(e : Expr) : Expr = e match {
   
    /*
     * Expressions with shortcutting etc. that handle errors specially
     */
    case IfExpr(BooleanLiteral(true), thenn, _) => thenn
    case IfExpr(BooleanLiteral(false), _, elze) => elze
    case IfExpr(e: Error, _, _) => e
    case ite : IfExpr => ite 

    case and@And(subs) => subs.toList match {
      case Nil => sys.error("And with empty args")
      case head :: Nil => head
      case BooleanLiteral(true) :: tail => And(subs.tail)
      case ( h@(BooleanLiteral(false)| Error(_)) ) :: _ => h 
      case _ => and
    }
    
    case or@Or(subs) => subs.toList match {
      case Nil => sys.error("Or with empty args")
      case head :: Nil => head
      case BooleanLiteral(false) :: tail => And(subs.tail)
      case ( h@(BooleanLiteral(true)| Error(_)) ) :: _ => h 
      case _ => or
    }

    // Implies is handled through Implies.apply method (with shortcutting)

    // As is the case with all expression types, does not manage to simplify 
    // in cases that require knowledge of path condition.
    case MatchExpr(scrut, cases) => {

      // Some(true) = patt matches with e
      // Some(false)= patt does not match with e
      // None = unknown
      def patternMatches(e : Expr, patt : Pattern) : Option[Boolean] = (e, patt) match {
        // Wildcard matches anything
        case (_, WildcardPattern(_)) => Some(true)
        
        // Case class matches with same class type if subpatterns also match
        case ( CaseClass(ct, args), CaseClassPattern(_, ct_ , subPatterns) ) if ct == ct_ =>
          val subJudgements = args zip subPatterns map { case (arg, patt) => patternMatches(arg, patt) } 
          if (subJudgements contains Some(false)) Some(false)
          else if (subJudgements contains None) None 
          else Some(true) 
        // Non-matching case classes
        case ( CaseClass(ct, _), CaseClassPattern(_, ct_ , _) ) if ct != ct_ =>
          Some(false)
        
        // We can judge about InstanceOfPattern iff the scrutinee type is a CaseClassType
        // FIXME ???
        case ( expr, InstanceOfPattern(_, ct) ) => {
          if (isSubtypeOf(expr.getType, ct)) Some(true)
          else {
            val tparams = (typeParameters(expr.getType) ++ typeParameters(ct)).toSeq
            if (canBeSubtypeOf(expr.getType,tparams, ct).isEmpty) Some(false)
            else None
          }
        }
        // Tuple and TuplePattern
        case ( Tuple(elems), TuplePattern(_, subPatterns) ) =>
          val subJudgements = elems zip subPatterns map { case (arg, patt) => patternMatches(arg, patt) } 
          if (subJudgements contains Some(false)) Some(false)
          else if (subJudgements contains None) None 
          else Some(true) 

        case ( l1: Literal[_], LiteralPattern(_, l2) ) => Some(l1 == l2)

        // We can judge about nothing else
        case _ => None
      }

      // Some(true) = cs matches with e
      // Some(false)= cs does not match with e
      // None = unknown
      def caseMatches(e : Expr, cs : MatchCase) = cs match {
        case SimpleCase( pattern, _ ) => patternMatches(e, pattern)
        case GuardedCase(pattern, guard, _) => 
          (patternMatches(e,pattern),guardPasses(guard, e, pattern)) match {
            case (Some(true), Some(true)) => Some(true)
            case (None, None) => None
            case _ => Some(false) 
          }
        }


      def inlineWithPattern( patt : Pattern, expr : Expr, into : Expr) : Expr = {
        
        require( patternMatches(expr,patt) getOrElse false )

        def onSubpatterns( subPatts: Seq[Pattern], subExpressions : Seq[Expr], initial : Expr) =  
          subPatts.zip(subExpressions).foldLeft(initial){ 
            case (current, (pt, e)) => inlineWithPattern(pt,e,current) 
          }

        def replaceBinder(binder : Option[Identifier], e : Expr, into : Expr) = binder match {
          case None => into
          case Some(bind) => replaceFromIDs(Map(bind -> e), into)
        }
        
        (patt,expr) match {
          case (_:WildcardPattern | _:InstanceOfPattern, _ ) =>
            replaceBinder(patt.binder, expr, into)
          case ( TuplePattern(binder, subPatts), Tuple(elems)) => 
            replaceBinder(binder, expr, onSubpatterns(subPatts, elems, into))
          case ( CaseClassPattern( binder, _, subPatts), CaseClass(_, args) ) =>
            replaceBinder(binder, expr, onSubpatterns(subPatts, args,  into))
          case  _ => into
        }
      }

      def guardPasses(guard : Expr, scrut : Expr, patt : Pattern) = {
        val inlined = inlineWithPattern(patt, scrut, guard)
        eval(inlined,mapping) match {
          case Successful(BooleanLiteral(b)) => Some(b)
          case _ => None
        }
      }

      cases flatMap { cse => caseMatches(scrut, cse) match {
        case Some(false) => None
        case other => Some(cse, other)
      }} match {
        case Nil => Error("Match failed!")
        case (cse, Some(true)) :: _ => inlineWithPattern(cse.pattern, scrut, cse.rhs)
        // If the first case is unknown, don't do any further 
        case cases => MatchExpr(scrut, cases.unzip._1)
      }
    }

    

    /* 
     * Generic handling if a (direct) subexpression is an error
     */
    case UnaryOperator(e : Error, _ ) => e
    case BinaryOperator(e : Error, _, _) => e
    case BinaryOperator(_, e : Error, _) => e
    case NAryOperator(operands, _) if operands exists { _.isInstanceOf[Error] } =>
      operands.find{ _.isInstanceOf[Error] }.get


    /*
     * If no direct subexpression is an error, treat each specific expression
     */

    /*
     * Assertions
     */
    case Require(BooleanLiteral(false), _) => Error("Precondition failed!")
    case Require(BooleanLiteral(true), body) => body

    // TODO: This is awkward. We don't want to desugar the postcondition, 
    // but then we have to call the recursive version of the function on the body
    case ens@Ensuring(body,id, pred) => 
      val inlinedPred = eval(replaceFromIDs(Map(id -> body), pred), mapping)
      inlinedPred match {
        case Successful(BooleanLiteral(true) ) => body
        case Successful(BooleanLiteral(false)) => Error("Postcondition failed!")
        case _ => ens
      }
    case Assert(BooleanLiteral(false), error, _) => Error(error getOrElse "Assertion failed!")
    case Assert(BooleanLiteral(true), _, body) => body
    
    // Error, NoTree, This cannot be evaluated further

    /* 
     * Local Definitions
     */
    case Let(binder, value, body) => replaceFromIDs(Map(binder -> value), body)

    case LetTuple(binders, Tuple(values), body) => replaceFromIDs((binders zip values).toMap,body)

    // LetDefs will be inlined in the call sites. So make sure you eliminate them if they are dead.
    case LetDef(fd, body) if !(variablesOf(body) contains fd.id) => body
    
    /*
     * Function/method invocations. We don't touch recursice functions/methods
     */
    case fi:FunctionInvocation if !program.callGraph.isRecursive(fi.tfd.fd) =>
      inlineFunction(fi)
    
    case mi:MethodInvocation if !program.callGraph.isRecursive(mi.tfd.fd) =>
      inlineMethod(mi)

    /* Tuples */
    // "Tuple" cannot be evaluated further
    case TupleSelect(Tuple(exprs), ind) if exprs forall errorFree => exprs(ind)

    /* Equality */
    case Equals(lhs, rhs) if isFullyEvaluated(lhs) && isFullyEvaluated(rhs) => 
      BooleanLiteral(lhs == rhs)
    case e@Equals(lhs, rhs) if errorFree(e) && lhs == rhs => 
      BooleanLiteral(true)


    /* Logic */
    // Not, Iff are handled through the respective .apply methods 

    /* Case classes */
    // CaseClassSelector is handled through the respective .apply method
    // FIXME does not respect errors though.
    // Case class cannot be evaluated further
    case CaseClassInstanceOf(ct, expr) if isFullyEvaluated(expr) =>
      BooleanLiteral(expr.getType == ct)
    case CaseClassInstanceOf(ct, expr) if errorFree(expr) && expr.getType == ct =>
      BooleanLiteral(true)

    /* Arithmetic */
    case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
    case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
    case UMinus(IntLiteral(i)) => IntLiteral(-i)
    case Times(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
    case Division(i, IntLiteral(0)) if errorFree(i) => Error("Division by zero!")
    case Division(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 / i2)
    case Modulo(i, IntLiteral(0)) if errorFree(i) => Error("Division by zero!")
    case Modulo(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 % i2)
    case LessThan(IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
    case GreaterThan(IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
    case LessEquals(IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
    case GreaterEquals(IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)

    // GenericValue and Literals are values

    /* Sets */
    case ElementOfSet(elem, FiniteSet(elems)) if elems + elem forall isFullyEvaluated =>
      BooleanLiteral(elems contains elem)
    case ElementOfSet(elem, FiniteSet(elems)) if (elems + elem forall errorFree) && (elems contains elem) =>
      BooleanLiteral(true)
    case SetCardinality(FiniteSet(elems)) if elems forall errorFree => 
      IntLiteral(elems.size)
    case SubsetOf(FiniteSet(subset), FiniteSet(superset)) if subset ++ superset forall isFullyEvaluated =>
      BooleanLiteral(subset subsetOf superset)
    case SetIntersection(FiniteSet(s1), FiniteSet(s2)) if s1 ++ s2 forall isFullyEvaluated =>
      FiniteSet(s1 & s2)
    case SetUnion(FiniteSet(s1), FiniteSet(s2)) if s1 ++ s2 forall isFullyEvaluated =>
      FiniteSet(s1 ++ s2)
    
    /* Maps */
    case MapGet(f@FiniteMap(singletons), e) if e +: keys(f) forall isFullyEvaluated =>
      singletons.toMap getOrElse (e, Error("Key not found in map"))
    case MapUnion(f1@FiniteMap(s1), f2@FiniteMap(s2)) if keys(f1) ++ keys(f2) forall isFullyEvaluated =>
      var m1 = s1.toMap
      s2 foreach { m1 += _ }
      FiniteMap(m1.toSeq)
    case MapDifference(f1@FiniteMap(s1), f2@FiniteMap(s2)) if keys(f1) ++ keys(f2) forall isFullyEvaluated =>
      var m1 = s1.toMap
      s2 foreach { m1 -= _._1 }
      FiniteMap(m1.toSeq)
    case MapIsDefinedAt(f@FiniteMap(s), e) if e +: keys(f) forall isFullyEvaluated =>
      BooleanLiteral(keys(f) contains e)
    case MapIsDefinedAt(f@FiniteMap(s), e) if (e +: keys(f) forall errorFree) && (keys(f) contains e) =>
      BooleanLiteral(true)

    case v@Variable(id) => mapping getOrElse (id, v)

    // TODO : Multisets, Arrays
    // TODO (?) : Distinct, WithOracle, Choose
    
    case other => other

  }


  def eval(e : Expr, mapping : Map[Identifier,Expr]) = try { 
    simplePreTransform(fixpoint(oneStep(mapping)))(e) match {
      case Error(msg) => RuntimeError(msg)
      case other => Successful(other)
    }
  } catch { 
    case _ : Throwable => 
      EvaluatorError("Partial evaluation failed!")
  }


}
