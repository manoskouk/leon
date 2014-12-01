/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import TypeTreeOps._
  import Definitions._
  import Extractors._
  import Constructors._


  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed with Serializable

  trait Terminal {
    self: Expr =>
  }

  case class NoTree(tpe: TypeTree) extends Expr with Terminal with Typed {
    val getType = tpe
  }

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(tpe: TypeTree, description: String) extends Expr with Terminal {
    val getType = tpe
  }

  case class Require(pred: Expr, body: Expr) extends Expr with Typed {
    def getType = body.getType
  }

  case class Ensuring(body: Expr, id: Identifier, pred: Expr) extends Expr {
    def getType = body.getType
  }

  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    def getType = body.getType
  }

  case class Passes(scrut: Expr, tests : List[MatchCase]) extends Expr {
    def getType = leastUpperBound(tests.map(_.rhs.getType)).getOrElse(Untyped)
  }

  case class Choose(vars: List[Identifier], pred: Expr) extends Expr with UnaryExtractable {
    assert(!vars.isEmpty)

    def getType = if (vars.size > 1) TupleType(vars.map(_.getType)) else vars.head.getType

    def extract = {
      Some((pred, (e: Expr) => Choose(vars, e).setPos(this)))
    }
  }

  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    def getType = body.getType
  }

  case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr {
    assert(value.getType.isInstanceOf[TupleType],
           "The definition value in LetTuple must be of some tuple type; yet we got [%s]. In expr: \n%s".format(value.getType, this))

    def getType = body.getType
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    def getType = body.getType
  }

  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    def getType = tfd.returnType
  }

  /**
   * OO Trees
   *
   * Both MethodInvocation and This get removed by phase MethodLifting. Methods become functions,
   * This becomes first argument, and MethodInvocation become FunctionInvocation.
   */
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    def getType = {
      // We need ot instanciate the type based on the type of the function as well as receiver
      val fdret = tfd.returnType
      val extraMap: Map[TypeParameterDef, TypeTree] = rec.getType match {
        case ct: ClassType =>
          (cd.tparams zip ct.tps).toMap  
        case _ =>
          Map()
      }

      instantiateType(fdret, extraMap)
    }
  }

  case class This(ct: ClassType) extends Expr with Terminal {
    def getType = ct
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    def getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped)
  }

  case class Tuple(exprs: Seq[Expr]) extends Expr {
    def getType = TupleType(exprs.map(_.getType))
  }

  // Index is 1-based, first element of tuple is 1.
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    assert(index >= 1)

    def getType = tuple.getType match {
      case TupleType(ts) =>
        assert(index <= ts.size)
        ts(index - 1)

      case _ =>
        Untyped
    }
  }

  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    assert(cases.nonEmpty)

    def getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(Untyped)
  }

  sealed abstract class MatchCase extends Tree {
    val pattern: Pattern
    val rhs: Expr
    val optGuard: Option[Expr]
    def expressions: Seq[Expr] = List(rhs) ++ optGuard
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase {
    val optGuard = None
  }

  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    val optGuard = Some(guard)
  }

  sealed abstract class Pattern extends Tree {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.map(_.binders).foldLeft[Set[Identifier]](Set.empty)(_ ++ _)
    def binders: Set[Identifier] = subBinders ++ binder.toSet

    def withBinder(b : Identifier) = { this match {
      case Pattern(None, subs, builder) => builder(Some(b), subs)
      case other => other
    }}.copiedFrom(this)
  }

  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern { // c: Class
    val subPatterns = Seq()
  }
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq()
  } 
  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern

  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern

  case class LiteralPattern[+T](binder: Option[Identifier], lit : Literal[T]) extends Pattern {
    val subPatterns = Seq()    
  }


  /* Propositional logic */
  case class And(exprs: Seq[Expr]) extends Expr {
    def getType = BooleanType

    assert(exprs.size >= 2)
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  case class Or(exprs: Seq[Expr]) extends Expr {
    def getType = BooleanType

    assert(exprs.size >= 2)
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    def getType = BooleanType
  }

  case class Not(expr: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Variable(id: Identifier) extends Expr with Terminal {
    private var _tpe = id.getType

    def setType(tpe: TypeTree): this.type = {
      _tpe = tpe
      this
    }

    def getType = _tpe
  }

  /* Literals */
  sealed abstract class Literal[+T] extends Expr with Terminal {
    val value: T
  }

  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
    val getType = tp
  }

  case class CharLiteral(value: Char) extends Literal[Char] {
    val getType = CharType
  }

  case class IntLiteral(value: Int) extends Literal[Int] {
    val getType = Int32Type
  }

  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    val getType = BooleanType
  }

  case class StringLiteral(value: String) extends Literal[String] with MutableTyped

  case class UnitLiteral() extends Literal[Unit] {
    val getType = UnitType
    val value = ()
  }

  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr {
    val getType = ct
  }

  case class CaseClassInstanceOf(classType: CaseClassType, expr: Expr) extends Expr {
    val getType = BooleanType
  }

  object CaseClassSelector {
    def apply(classType: CaseClassType, caseClass: Expr, selector: Identifier): Expr = {
      caseClass match {
        case CaseClass(ct, fields) =>
          if (ct.classDef == classType.classDef) {
            fields(ct.classDef.selectorID2Index(selector))
          } else {
            new CaseClassSelector(classType, caseClass, selector)
          }
        case _ => new CaseClassSelector(classType, caseClass, selector)
      }
    }

    def unapply(ccs: CaseClassSelector): Option[(CaseClassType, Expr, Identifier)] = {
      Some((ccs.classType, ccs.caseClass, ccs.selector))
    }
  }

  class CaseClassSelector(val classType: CaseClassType, val caseClass: Expr, val selector: Identifier) extends Expr {
    val selectorIndex = classType.classDef.selectorID2Index(selector)
    def getType = classType.fieldsTypes(selectorIndex)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: CaseClassSelector => (t.classType, t.caseClass, t.selector) == (classType, caseClass, selector)
      case _ => false
    })

    override def hashCode: Int = (classType, caseClass, selector).hashCode + 9
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class UMinus(expr: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = BooleanType
  }
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = BooleanType
  }
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = BooleanType
  }
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }

  /* Set expressions */
  case class FiniteSet(elements: Set[Expr]) extends Expr with MutableTyped {
    val tpe = if (elements.isEmpty) None else leastUpperBound(elements.toSeq.map(_.getType))
    tpe.filter(_ != Untyped).foreach(t => setType(SetType(t)))
  }

  case class ElementOfSet(element: Expr, set: Expr) extends Expr {
    val getType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr {
    val getType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr {
    val getType  = BooleanType
  }

  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }

  /* Map operations. */
  case class FiniteMap(singletons: Seq[(Expr, Expr)]) extends Expr with MutableTyped
  case class MapGet(map: Expr, key: Expr) extends Expr {
    def getType = map.getType match {
      case MapType(from, to) => to
      case _ => Untyped
    }
  }
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(Untyped)
  }
  case class MapDifference(map: Expr, keys: Expr) extends Expr with MutableTyped
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr {
    val getType = BooleanType
  }

  /* Array operations */

  case class ArraySelect(array: Expr, index: Expr) extends Expr {
    def getType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        Untyped
    }
  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    def getType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType(_)).getOrElse(Untyped)
      case _ =>
        Untyped
    }
  }

  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  case class FiniteArray(exprs: Seq[Expr]) extends Expr with MutableTyped

  /* Special trees */

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with UnaryExtractable {
    assert(!oracles.isEmpty)

    def getType = body.getType

    def extract = {
      Some((body, (e: Expr) => WithOracle(oracles, e).setPos(this)))
    }
  }

  case class Hole(tpe: TypeTree, alts: Seq[Expr]) extends Expr with NAryExtractable {
    val getType = tpe

    def extract = {
      Some((alts, (es: Seq[Expr]) => Hole(tpe, es).setPos(this)))
    }
  }

  case class RepairHole(tpe: TypeTree, components: Seq[Expr]) extends Expr with NAryExtractable {
    val getType = tpe

    def extract = {
      Some((components, (es: Seq[Expr]) => RepairHole(tpe, es).setPos(this)))
    }
  }

  /**
   * DEPRECATED TREES
   * These trees are not guaranteed to be supported by Leon.
   **/
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr {
    def getType = ArrayType(defaultValue.getType)
  }

  case class SetMin(set: Expr) extends Expr {
    val getType = Int32Type
  }

  case class SetMax(set: Expr) extends Expr {
    val getType = Int32Type
  }

  case class EmptyMultiset(baseType: TypeTree) extends Expr with Terminal {
    val getType = MultisetType(baseType)
  }
  case class FiniteMultiset(elements: Seq[Expr]) extends Expr {
    assert(elements.size > 0)
    def getType = MultisetType(leastUpperBound(elements.map(_.getType)).getOrElse(Untyped))
  }
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  case class MultisetCardinality(multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr  {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr { // disjoint union 
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr  {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetToSet(multiset: Expr) extends Expr {
    def getType = multiset.getType match {
      case MultisetType(base) => SetType(base)
      case _ => Untyped
    }
  }


}
