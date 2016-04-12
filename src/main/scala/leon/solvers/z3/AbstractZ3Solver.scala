/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers.z3

import com.microsoft.z3.{ Solver => _, _ }
import com.microsoft.z3.enumerations.Z3_ast_kind
import solvers.{Constructor => _, Model => _, _}
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Expressions.{Expr => LeonExpr, _}
import purescala.TypeOps._
import purescala.ExprOps._
import purescala.Types._

import utils._

import scala.collection.JavaConversions._
import scala.language.implicitConversions

case class UnsoundExtractionException(ast: AST, msg: String)
  extends Exception("Can't extract " + ast + " : " + msg)
// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait AbstractZ3Solver extends Solver {

  val program : Program

  val library = program.library

  protected val reporter : Reporter = context.reporter

  context.interruptManager.registerForInterrupts(this)

  private[this] var freed = false

  protected def unsound(ast: AST, msg: String): Nothing =
    throw UnsoundExtractionException(ast, msg)

  override def finalize() {
    if (!freed) {
      reporter.warning("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      (new Exception).printStackTrace() // FIXME is this really the trace we want to print?
      free()
    }
  }

  private val z3cfg = {
    Map[String, String](
      "model" -> "true",
      "type_check" -> "true",
      "well_sorted_check" -> "true"
    )
  }
  Global.ToggleWarningMessages(true)

  protected[leon] var z3: Context = null

  lazy protected val solver = z3.mkSolver()

  override def free(): Unit = {
    freed = true
    if (z3 ne null) {
      z3.dispose()
      z3 = null
    }
  }

  override def interrupt(): Unit = {
    if(z3 ne null) {
      z3.interrupt()
    }
  }

  override def recoverInterrupt(): Unit = ()

  def functionDefToDecl(tfd: TypedFunDef): FuncDecl = {
    functions.cachedB(tfd) {
      val sortSeq    = tfd.params.map(vd => typeToSort(vd.getType))
      val returnSort = typeToSort(tfd.returnType)

      z3.mkFreshFuncDecl(tfd.id.uniqueName, sortSeq.toArray, returnSort)
    }
  }

  // ADT Manager
  protected val adtManager = new ADTManager(context)

  // Bijections between Leon Types/Functions/Ids to Z3 Sorts/Decls/ASTs
  protected val functions = new IncrementalBijection[TypedFunDef, FuncDecl]()
  protected val lambdas   = new IncrementalBijection[FunctionType, FuncDecl]()
  protected val variables = new IncrementalBijection[LeonExpr, Expr]()

  protected val constructors = new IncrementalBijection[TypeTree, FuncDecl]()
  protected val selectors    = new IncrementalBijection[(TypeTree, Int), FuncDecl]()
  protected val testers      = new IncrementalBijection[TypeTree, FuncDecl]()

  protected val sorts     = new IncrementalMap[TypeTree, Sort]()

  var isInitialized = false
  protected[leon] def initZ3(): Unit = {
    if (!isInitialized) {
      val timer = context.timers.solvers.z3.init.start()

      z3 = new Context(z3cfg)

      functions.clear()
      lambdas.clear()
      variables.clear()
      constructors.clear()
      selectors.clear()
      testers.clear()
      sorts.reset()

      prepareSorts()

      isInitialized = true

      timer.stop()
    }
  }

  initZ3()

  def rootType(ct: TypeTree): TypeTree = ct match {
    case ct: ClassType => ct.root
    case t => t
  }

  def declareStructuralSort(t: TypeTree): Sort = {
    //println("///"*40)
    //println("Declaring for: "+t)

    adtManager.defineADT(t) match {
      case Left(adts) =>
        declareDatatypes(adts.toSeq)
        sorts(normalizeType(t))

      case Right(conflicts) =>
        conflicts.foreach { declareStructuralSort }
        declareStructuralSort(t)
    }
  }

  sealed abstract class ADTSortReference
  case class RecursiveType(index: Int) extends ADTSortReference
  case class RegularSort(sort: Sort) extends ADTSortReference

  def mkDatatypeSorts(defs: Seq[(String, Seq[String], Seq[Seq[(String,ADTSortReference)]])]): 
      Seq[(Sort, Seq[FuncDecl], Seq[FuncDecl], Seq[Seq[FuncDecl]])] = {

    val typeCount: Int = defs.size

    // the following big block builds the following three lists
    val (symbolList, constructorList) = (for((typeName, typeConstructorNames, typeConstructorArgs) <- defs) yield {
      val constructorCount: Int = typeConstructorNames.size
      if(constructorCount != typeConstructorArgs.size) {
        throw new IllegalArgumentException(
          "sequence of constructor names should have the same size as sequence of constructor param lists, for type " + typeName
        )
      }

      val sym: Symbol = z3.mkSymbol(typeName)

      val constructors = for ((tcn, tca) <- typeConstructorNames zip typeConstructorArgs) yield {
        val constructorSym: Symbol = z3.mkSymbol(tcn)
        val testSym: Symbol = z3.mkSymbol("is" + tcn)
        val fieldSyms: Array[Symbol] = tca.map(p => z3.mkSymbol(p._1)).toArray
        val fieldSorts: Array[Sort] = tca.map(p => p._2 match {
          case RecursiveType(idx) if idx >= typeCount =>
            throw new IllegalArgumentException(
              "index of recursive type is too big (" + idx + ") for field " + p._1 + " of type " + typeName
            )
          case RegularSort(srt) => srt
          case RecursiveType(_) => null
        }).toArray

        val fieldRefs: Array[Int] = tca.map(p => p._2 match {
          case RegularSort(_) => 0
          case RecursiveType(idx) => idx
        }).toArray

        z3.mkConstructor(constructorSym, testSym, fieldSyms, fieldSorts, fieldRefs)
      }

      (sym, constructors.toArray)
    }).unzip
  
    val constructorMatrix: Array[Array[Constructor]] = constructorList.toArray

    val newSorts = z3.mkDatatypeSorts(symbolList.toArray, constructorMatrix)

    for((sort, consLst) <- (newSorts zip constructorMatrix)) yield {
      val zipped = for (cons <- consLst) yield {
        val consFun = cons.ConstructorDecl()
        val testFun = cons.getTesterDecl
        val selectors = if (cons.getNumFields > 0) cons.getAccessorDecls.toList else Nil
        (consFun, testFun, selectors)
      }

      val (consFuns, testFuns, selectorFunss) = zipped.unzip3

      (sort, consFuns.toList, testFuns.toList, selectorFunss.toList)
    }
  }


  def declareDatatypes(adts: Seq[(TypeTree, DataType)]): Unit = {

    val indexMap: Map[TypeTree, Int] = adts.map(_._1).zipWithIndex.toMap

    def typeToSortRef(tt: TypeTree): ADTSortReference = {
      val tpe = rootType(tt)

      if (indexMap contains tpe) {
        RecursiveType(indexMap(tpe))
      } else {
        RegularSort(typeToSort(tt))
      }
    }

    // Define stuff
    val defs = for ((_, DataType(sym, cases)) <- adts) yield {(
      sym.uniqueName,
      cases.map(c => c.sym.uniqueName),
      cases.map(c => c.fields.map{ case(id, tpe) => (id.uniqueName, typeToSortRef(tpe))})
    )}

    val resultingZ3Info = mkDatatypeSorts(defs)

    for ((z3Inf, (tpe, DataType(sym, cases))) <- resultingZ3Info zip adts) {
      val (name, consFuns, testFuns, selFuns) = z3Inf
      sorts += (tpe -> name)
      assert(cases.size == consFuns.size)

      for ((c, (consFun, testFun)) <- cases zip (consFuns zip testFuns)) {
        testers += (c.tpe -> testFun)
        constructors += (c.tpe -> consFun)
      }

      for ((c, fieldFuns) <- cases zip selFuns) {
        assert(c.fields.size == fieldFuns.size)

        for ((selFun, index) <- fieldFuns.zipWithIndex) {
          selectors += (c.tpe, index) -> selFun
        }
      }
    }
  }

  // Prepares some of the Z3 sorts, but *not* the tuple sorts; these are created on-demand.
  private def prepareSorts(): Unit = {
    sorts += Int32Type   -> z3.mkBitVecSort(32)
    sorts += CharType    -> z3.mkBitVecSort(32) // FIXME is that correct?
    sorts += IntegerType -> z3.mkIntSort
    sorts += RealType    -> z3.mkRealSort
    sorts += BooleanType -> z3.mkBoolSort

    testers.clear()
    constructors.clear()
    selectors.clear()
  }

  def normalizeType(t: TypeTree): TypeTree = {
    bestRealType(t)
  }

  // assumes prepareSorts has been called....
  protected[leon] def typeToSort(oldtt: TypeTree): Sort = normalizeType(oldtt) match {
    case Int32Type | BooleanType | IntegerType | RealType | CharType =>
      sorts(oldtt)

    case tpe @ (_: ClassType  | _: ArrayType | _: TupleType | _: TypeParameter | UnitType) =>
      sorts.cached(tpe) {
        declareStructuralSort(tpe)
      }

    case tt @ SetType(base) =>
      sorts.cached(tt) {
        z3.mkSetSort(typeToSort(base))
      }

    case tt @ MapType(fromType, toType) =>
      typeToSort(RawArrayType(fromType, library.optionType(toType)))

    case rat @ RawArrayType(from, to) =>
      sorts.cached(rat) {
        val fromSort = typeToSort(from)
        val toSort = typeToSort(to)

        z3.mkArraySort(fromSort, toSort)
      }

    case ft @ FunctionType(from, to) =>
      sorts.cached(ft) {
        val symbol = z3.mkSymbol(ft.toString) // FIXME Is this right??? does it freshen?
        z3.mkUninterpretedSort(symbol)
      }

    case other =>
      unsupported(other)
  }

  protected implicit def statusToBoolean(st: Status): Option[Boolean] = st match {
    case Status.SATISFIABLE   => Some(true)
    case Status.UNSATISFIABLE => Some(false)
    case Status.UNKNOWN       => None
  }

  @inline protected implicit def castDownBool (z3e: Expr): BoolExpr   = z3e.asInstanceOf[BoolExpr]
  @inline protected implicit def castDownArith(z3e: Expr): ArithExpr  = z3e.asInstanceOf[ArithExpr]
  @inline protected implicit def castDownBV   (z3e: Expr): BitVecExpr = z3e.asInstanceOf[BitVecExpr]
  @inline protected implicit def castDownArr  (z3e: Expr): ArrayExpr  = z3e.asInstanceOf[ArrayExpr]

  protected[leon] def toZ3Formula(expr: LeonExpr, initialMap: Map[Identifier, Expr] = Map.empty): Expr = {

    var z3Vars: Map[Identifier, Expr] = if (initialMap.nonEmpty) {
      initialMap
    } else {
      // FIXME TODO pleeeeeeeease make this cleaner. Ie. decide what set of
      // variable has to remain in a map etc.
      variables.aToB.collect{ case (Variable(id), p2) => id -> p2 }
    }

    def rec(ex: LeonExpr): Expr = ex match {

      // TODO: Leave that as a specialization?
      case LetTuple(ids, e, b) =>
        z3Vars = z3Vars ++ ids.zipWithIndex.map { case (id, ix) =>
          val entry = id -> rec(tupleSelect(e, ix + 1, ids.size))
          entry
        }
        val rb = rec(b)
        z3Vars = z3Vars -- ids
        rb

      case p @ Passes(_, _, _) =>
        rec(p.asConstraint)

      case me @ MatchExpr(s, cs) =>
        rec(matchToIfThenElse(me))

      case Let(i, e, b) =>
        val re = rec(e)
        z3Vars = z3Vars + (i -> re)
        val rb = rec(b)
        z3Vars = z3Vars - i
        rb

      case a @ Assert(cond, err, body) =>
        rec(IfExpr(cond, body, Error(a.getType, err.getOrElse("Assertion failed")).setPos(a.getPos)).setPos(a.getPos))

      case e @ Error(tpe, _) =>
        val newAST = z3.mkFreshConst("errorValue", typeToSort(tpe))
        // Might introduce dupplicates (e), but no worries here
        variables += (e -> newAST)
        newAST

      case v @ Variable(id) => z3Vars.getOrElse(id,
        variables.getB(v).getOrElse {
          val newAST = z3.mkFreshConst(id.uniqueName, typeToSort(v.getType))
          z3Vars = z3Vars + (id -> newAST)
          variables += (v -> newAST)
          newAST
        }
      )

      case ite @ IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec(_): BoolExpr): _*)
      case Or(exs) => z3.mkOr(exs.map(rec(_): BoolExpr): _*)
      case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
      case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case IntLiteral(v) => z3.mkBV(v, 32) // FIXME 32?
      case InfiniteIntegerLiteral(v) => z3.mkNumeral(v.toString, typeToSort(IntegerType))
      case FractionalLiteral(n, d) => z3.mkNumeral(s"$n / $d", typeToSort(RealType))
      case CharLiteral(c) => z3.mkBV(c, 32)// FIXME
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l, r) => z3.mkEq(rec( l ), rec( r ) )
      case Plus(l, r) => z3.mkAdd(rec(l), rec(r))
      case Minus(l, r) => z3.mkSub(rec(l), rec(r))
      case Times(l, r) => z3.mkMul(rec(l), rec(r))
      case Division(l, r) =>
        val rl = rec(l)
        val rr = rec(r)
        z3.mkITE(
          z3.mkGe(rl, z3.mkNumeral("0", typeToSort(IntegerType))),
          z3.mkDiv(rl, rr),
          z3.mkUnaryMinus(z3.mkDiv(z3.mkUnaryMinus(rl), rr))
        )
      case Remainder(l, r) =>
        val q = rec(Division(l, r))
        z3.mkSub(rec(l), z3.mkMul(rec(r), q))
      case Modulo(l, r) =>
        z3.mkMod(rec(l).asInstanceOf[IntExpr], rec(r).asInstanceOf[IntExpr])
      case UMinus(e) => z3.mkUnaryMinus(rec(e))

      case RealPlus(l, r) => z3.mkAdd(rec(l), rec(r))
      case RealMinus(l, r) => z3.mkSub(rec(l), rec(r))
      case RealTimes(l, r) => z3.mkMul(rec(l), rec(r))
      case RealDivision(l, r) => z3.mkDiv(rec(l), rec(r))
      case RealUMinus(e) => z3.mkUnaryMinus(rec(e))

      case BVPlus(l, r) => z3.mkBVAdd(rec(l), rec(r))
      case BVMinus(l, r) => z3.mkBVSub(rec(l), rec(r))
      case BVTimes(l, r) => z3.mkBVMul(rec(l), rec(r))
      case BVDivision(l, r) => z3.mkBVSDiv(rec(l), rec(r))
      case BVRemainder(l, r) => z3.mkBVSRem(rec(l), rec(r))
      case BVUMinus(e) => z3.mkBVNeg(rec(e))
      case BVNot(e) => z3.mkBVNot(rec(e))
      case BVAnd(l, r) => z3.mkBVAND(rec(l), rec(r))
      case BVOr(l, r) => z3.mkBVOR(rec(l), rec(r))
      case BVXOr(l, r) => z3.mkBVXOR(rec(l), rec(r))
      case BVShiftLeft(l, r) => z3.mkBVSHL(rec(l), rec(r))
      case BVAShiftRight(l, r) => z3.mkBVASHR(rec(l), rec(r))
      case BVLShiftRight(l, r) => z3.mkBVLSHR(rec(l), rec(r))
      case LessThan(l, r) => l.getType match {
        case IntegerType => z3.mkLt(rec(l), rec(r))
        case RealType => z3.mkLt(rec(l), rec(r))
        case Int32Type => z3.mkBVSLT(rec(l), rec(r))
        case CharType => z3.mkBVSLT(rec(l), rec(r))
      }
      case LessEquals(l, r) => l.getType match {
        case IntegerType => z3.mkLe(rec(l), rec(r))
        case RealType => z3.mkLe(rec(l), rec(r))
        case Int32Type => z3.mkBVSLE(rec(l), rec(r))
        case CharType => z3.mkBVSLE(rec(l), rec(r))
        //case _ => throw new IllegalStateException(s"l: $l, Left type: ${l.getType} Expr: $ex")
      }
      case GreaterThan(l, r) => l.getType match {
        case IntegerType => z3.mkGt(rec(l), rec(r))
        case RealType => z3.mkGt(rec(l), rec(r))
        case Int32Type => z3.mkBVSGT(rec(l), rec(r))
        case CharType => z3.mkBVSGT(rec(l), rec(r))
      }
      case GreaterEquals(l, r) => l.getType match {
        case IntegerType => z3.mkGe(rec(l), rec(r))
        case RealType => z3.mkGe(rec(l), rec(r))
        case Int32Type => z3.mkBVSGE(rec(l), rec(r))
        case CharType => z3.mkBVSGE(rec(l), rec(r))
      }

      case u : UnitLiteral =>
        val tpe = normalizeType(u.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor()

      case t @ Tuple(es) =>
        val tpe = normalizeType(t.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor(es.map(rec): _*)

      case ts @ TupleSelect(t, i) =>
        val tpe = normalizeType(t.getType)
        typeToSort(tpe)
        val selector = selectors.toB((tpe, i-1))
        selector(rec(t))

      case c @ CaseClass(ct, args) =>
        typeToSort(ct) // Making sure the sort is defined
        val constructor = constructors.toB(ct)
        constructor(args.map(rec): _*)

      case c @ CaseClassSelector(cct, cc, sel) =>
        typeToSort(cct) // Making sure the sort is defined
        val selector = selectors.toB(cct, c.selectorIndex)
        selector(rec(cc))

      case AsInstanceOf(expr, ct) =>
        rec(expr)

      case IsInstanceOf(e, act: AbstractClassType) =>
        act.knownCCDescendants match {
          case Seq(cct) =>
            rec(IsInstanceOf(e, cct))
          case more =>
            val i = FreshIdentifier("e", act, alwaysShowUniqueID = true)
            rec(Let(i, e, orJoin(more map(IsInstanceOf(Variable(i), _)))))
        }

      case IsInstanceOf(e, cct: CaseClassType) =>
        typeToSort(cct) // Making sure the sort is defined
        val tester = testers.toB(cct)
        tester(rec(e))

      case al @ ArraySelect(a, i) =>
        val tpe = normalizeType(a.getType)

        val sa = rec(a)
        val content = selectors.toB((tpe, 1))(sa)

        z3.mkSelect(content, rec(i))

      case al @ ArrayUpdated(a, i, e) =>
        val tpe = normalizeType(a.getType)

        val sa = rec(a)
        val ssize    = selectors.toB((tpe, 0))(sa)
        val scontent = selectors.toB((tpe, 1))(sa)

        val newcontent = z3.mkStore(scontent, rec(i), rec(e))

        val constructor = constructors.toB(tpe)

        constructor(ssize, newcontent)

      case al @ ArrayLength(a) =>
        val tpe = normalizeType(a.getType)
        val sa = rec(a)
        selectors.toB((tpe, 0))(sa)

      case arr @ FiniteArray(elems, oDefault, length) =>
        val at @ ArrayType(base) = normalizeType(arr.getType)
        typeToSort(at)

        val default = oDefault.getOrElse(simplestValue(base))

        val ar = rec(RawArrayValue(Int32Type, elems.map {
          case (i, e) => IntLiteral(i) -> e
        }, default))

        constructors.toB(at)(rec(length), ar)

      case f @ FunctionInvocation(tfd, args) =>
        z3.mkApp(functionDefToDecl(tfd), args.map(rec): _*)

      case fa @ Application(caller, args) =>
        val ft @ FunctionType(froms, to) = normalizeType(caller.getType)
        val funDecl = lambdas.cachedB(ft) {
          val sortSeq    = (ft +: froms).map(tpe => typeToSort(tpe))
          val returnSort = typeToSort(to)

          val name = FreshIdentifier("dynLambda").uniqueName
          z3.mkFreshFuncDecl(name, sortSeq.toArray, returnSort)
        }
        z3.mkApp(funDecl, (caller +: args).map(rec): _*)

      case ElementOfSet(e, s) => z3.mkSetMembership(rec(e), rec(s))
      case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
      case SetIntersection(s1, s2) => z3.mkSetIntersection(rec(s1), rec(s2))
      case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
      case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
      case f @ FiniteSet(elems, base) => elems.foldLeft(z3.mkEmptySet(typeToSort(base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))

      case RawArrayValue(keyTpe, elems, default) =>
        val ar = z3.mkConstArray(typeToSort(keyTpe), rec(default))

        elems.foldLeft(ar) {
          case (array, (k, v)) => z3.mkStore(array, rec(k), rec(v))
        }

      /**
       * ===== Map operations =====
       */
      case m @ FiniteMap(elems, from, to) =>
        val MapType(_, t) = normalizeType(m.getType)

        rec(RawArrayValue(from, elems.map{
          case (k, v) => (k, CaseClass(library.someType(t), Seq(v)))
        }, CaseClass(library.noneType(t), Seq())))

      case MapApply(m, k) =>
        val mt @ MapType(_, t) = normalizeType(m.getType)
        typeToSort(mt)

        val el = z3.mkSelect(rec(m), rec(k))

        // Really ?!? We don't check that it is actually != None?
        selectors.toB(library.someType(t), 0)(el)

      case MapIsDefinedAt(m, k) =>
        val mt @ MapType(_, t) = normalizeType(m.getType)
        typeToSort(mt)

        val el = z3.mkSelect(rec(m), rec(k))

        testers.toB(library.someType(t))(el)

      case MapUnion(m1, FiniteMap(elems, _, _)) =>
        val mt @ MapType(_, t) = normalizeType(m1.getType)
        typeToSort(mt)

        elems.foldLeft(rec(m1)) { case (m, (k,v)) =>
          z3.mkStore(m, rec(k), rec(CaseClass(library.someType(t), Seq(v))))
        }

      case gv @ GenericValue(tp, id) =>
        typeToSort(tp)
        val constructor = constructors.toB(tp)
        constructor(rec(InfiniteIntegerLiteral(id)))

      case other =>
        unsupported(other)
    }

    rec(expr)
  }

  protected[leon] def fromZ3Formula(model: Model, tree: Expr, tpe: TypeTree): LeonExpr = {

    def rec(t: Expr, tpe: TypeTree): LeonExpr = {
      t match {
        case i: IntNum =>
          tpe match {
            case Int32Type =>
              // Dirty hack: .toInt would interpret as signed and fail for big integers,
              // but .toLong will give a large enough long and .toInt will just keep the lower bits
              IntLiteral(i.getInt64.toInt)
            case CharType  => CharLiteral(i.getInt.toChar)
            case IntegerType => InfiniteIntegerLiteral(i.getBigInteger)
            case other =>
              unsupported(other, "Unexpected type for integral value: " + other)
          }

        case _ if t.isUMinus =>
          UMinus(rec(t.getArgs()(0), tpe))
        case bv: BitVecNum =>
          // Dirty hack: .toInt would interpret as signed and fail for big integers,
          // but .toLong will give a large enough long and .toInt will just keep the lower bits
          tpe match {
            case Int32Type => IntLiteral(bv.getLong.toInt)
            case CharType => CharLiteral(bv.getInt.toChar)
          }
        case r: RatNum =>
          FractionalLiteral(r.getBigIntNumerator, r.getBigIntDenominator)

        case b: BoolExpr if b.isFalse =>
          BooleanLiteral(false)
        case b: BoolExpr if b.isTrue =>
          BooleanLiteral(true)

        case _ if tpe == UnitType =>
          UnitLiteral()

        case _ if t.getASTKind == Z3_ast_kind.Z3_VAR_AST && (variables containsB t) =>
          variables.toA(t)

        case _ if t.getASTKind == Z3_ast_kind.Z3_APP_AST && t.getArgs.isEmpty && (variables containsB t) =>
          variables.toA(t)

        case _ if t.isApp =>
          val decl = t.getFuncDecl
          val args = t.getArgs
          val argsSize = args.size
          if(functions containsB decl) {
            val tfd = functions.toA(decl)
            assert(tfd.params.size == argsSize)
            FunctionInvocation(tfd, args.zip(tfd.params).map{ case (a, p) => rec(a, p.getType) })
          } else if (constructors containsB decl) {
            constructors.toA(decl) match {
              case cct: CaseClassType =>
                CaseClass(cct, args.zip(cct.fieldsTypes).map { case (a, t) => rec(a, t) })

              case TupleType(ts) =>
                tupleWrap(args.zip(ts).map { case (a, t) => rec(a, t) })

              case ArrayType(to) =>
                val size = rec(args(0), Int32Type)
                val map  = rec(args(1), RawArrayType(Int32Type, to))

                (size, map) match {

                  case (s : IntLiteral, RawArrayValue(_, elems, default)) =>

                    if (s.value < 0)
                      unsupported(s, s"Z3 returned array of negative size")

                    val entries = elems.map {
                      case (IntLiteral(i), v) => i -> v
                      case (e,_) => unsupported(e, s"Z3 returned unexpected array index ${e.asString}")
                    }

                    finiteArray(entries, Some(default, s), to)
                  case (s : IntLiteral, arr) => unsound(args(1), "invalid array type")
                  case (size, _) => unsound(args(0), "invalid array size")
                }

              case tp @ TypeParameter(id) =>
                val InfiniteIntegerLiteral(n) = rec(args(0), IntegerType)
                GenericValue(tp, n.toInt)

              case t =>
                unsupported(t, "Woot? structural type that is non-structural")
            }
          } else {
            tpe match {
              case RawArrayType(from, to) =>
                val arrayFun = model.eval(t, false) // (_ as-array k)
                  .getFuncDecl // as-array k
                  .getParameters()(0).getFuncDecl // k
                Option(model.getFuncInterp(arrayFun)) match {
                  case None => unsound(t, "Couldn't find array!")
                  case Some(interp) =>
                    val entries = interp.getEntries.map { case entry =>
                      val index = rec(entry.getArgs()(0), IntegerType)
                      val value = rec(entry.getValue, to)
                      index -> value
                    }.toMap
                    val default = rec(interp.getElse, to)
                    RawArrayValue(from, entries, default)
                }

              case ft @ FunctionType(fts, tt) =>
                import scala.util.Try
                (for {
                  decl <- lambdas.getB(ft)
                  interp <- Try(model.getFuncInterp(decl)).toOption
                } yield {
                  val entries = interp.getEntries.toList.map { case entry =>
                    val args = entry.getArgs.toList.zip(fts) map (rec _).tupled
                    val value = rec(entry.getValue, tt)
                    args.toList -> value
                  }
                  val default = rec(interp.getElse, tt)
                  FiniteLambda(entries, default, ft)
                }).getOrElse(simplestValue(ft))

              case MapType(from, to) =>
                rec(t, RawArrayType(from, library.optionType(to))) match {
                  case r: RawArrayValue =>
                    // We expect a RawArrayValue with keys in from and values in Option[to],
                    // with default value == None
                    if (r.default.getType != library.noneType(to)) {
                      unsupported(r, "Solver returned a co-finite Map which is not supported.")
                    }
                    require(r.keyTpe == from, s"Type error in solver model, expected ${from.asString}, found ${r.keyTpe.asString}")

                    val elems = r.elems.flatMap {
                      case (k, CaseClass(leonSome, Seq(x))) => Some(k -> x)
                      case (k, _) => None
                    }

                    FiniteMap(elems, from, to)
                }

              case tpe @ SetType(dt) =>
                Option(model.getFuncInterp(t.getFuncDecl)) match {
                  case None => unsound(t, "???")
                  case Some(interp) =>
                    val entries = interp.getEntries
                    val elseValue = interp.getElse
                    if (rec(elseValue, BooleanType) == BooleanLiteral(true)) {
                      FiniteSet(entries.toSet flatMap { (entry: FuncInterp#Entry) =>
                        val elem = rec(entry.getArgs()(0), dt)
                        val value = rec(entry.getValue, BooleanType)
                        (value == BooleanLiteral(true)).option(elem)
                      }, dt)
                    } else {
                      unsound(t, "Co-finite set!?")
                    }
                }
              case _ => unsound(t, "unexpected AST")
            }
          }
        case _ => unsound(t, "unexpected AST")
      }
    }

    rec(tree, normalizeType(tpe))
  }

  protected[leon] def softFromZ3Formula(model: Model, tree: Expr, tpe: TypeTree) : Option[LeonExpr] = {
    try {
      Some(fromZ3Formula(model, tree, tpe))
    } catch {
      case e: Unsupported => None
      case e: UnsoundExtractionException => None
      case n: java.lang.NumberFormatException => None
    }
  }

  def idToFreshZ3Id(id: Identifier): Expr = {
    z3.mkFreshConst(id.uniqueName, typeToSort(id.getType))
  }

  def reset(): Unit = {
    throw new CantResetException(this)
  }

}
