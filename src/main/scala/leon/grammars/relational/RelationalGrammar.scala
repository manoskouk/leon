package leon.grammars
package relational

import leon.LeonContext
import leon.grammars.aspects.{Sized, TypeDepthBound}
import leon.purescala.Constructors._
import leon.purescala.Expressions.{Error, Expr}
import leon.purescala.Types._
import leon.purescala.TypeOps._
import leon.purescala.Common._
import leon.purescala.Definitions.TypeParameterDef
import leon.purescala.{PrettyPrintable, PrinterContext}
import leon.purescala.PrinterHelpers._
import leon.utils.SeqUtils

object RelationalAlg {

  def flatten(tps: Seq[TypeTree]): TypeTree = {
    require(tps.nonEmpty)
    tps match {
      case Seq(one) => one
      case more =>
        TupleType(more flatMap {
          case TupleType(subs) => subs
          case other => Seq(other)
        })
    }
  }

  trait RelExpr extends Expr with PrettyPrintable {
    override def isSimpleExpr = true
    override def printRequiresParentheses(within: Option[Tree]) = true
  }

  case class Union(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 + $e2"
    }
  }
  case class Inters(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 & $e2"
    }
  }
  case class Diff(e1: Expr, e2: Expr) extends RelExpr {
    require(e1.getType == e2.getType)
    val getType = e1.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 - $e2"
    }
  }

  case class Cross(e1: Expr, e2: Expr) extends RelExpr {
    val getType = flatten(Seq(e1.getType, e2.getType))
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 -> $e2"
    }
  }

  case class Join(e1: Expr, e2: Expr) extends RelExpr {
    val getType = (e1.getType, e2.getType) match {
      case (TupleType(tps1), TupleType(tps2)) if tps1.last == tps2.head =>
        TupleType(tps1.init ++ tps2.tail)
      case (TupleType(tps), other) if other == tps.last =>
        TupleType(tps.init)
      case (other, TupleType(tps)) if other == tps.head =>
        TupleType(tps.tail)
      case (t1, t2) =>
        println(t1, t2)
        ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$e1 . $e2"
    }
  }

  case class Transpose(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) => TupleType(Seq(t2, t1))
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"~$e1"
    }
  }
  case class RefTransClosure(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) if t1 == t2 => e1.getType
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"^$e1"
    }
  }

  case class TransClosure(e1: Expr) extends RelExpr {
    val getType = e1.getType match {
      case TupleType(Seq(t1, t2)) if t1 == t2 => e1.getType
      case _ => ???
    }
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"*$e1"
    }
  }



  case class Variable(id: Identifier) extends RelExpr {
    val getType = id.getType
    def printWith(implicit pctx: PrinterContext): Unit = {
      p"$id"
    }
  }

  trait RelType extends TypeTree with PrettyPrintable {

    def printWith(implicit pctx: PrinterContext): Unit = {
      val cn = this.getClass.getCanonicalName
      val n = cn.substring(cn.lastIndexOf(".")).tail.init
      p"$n"
    }

  }

  object S extends RelType
  object T extends RelType

}

import RelationalAlg._

case class RelationalGrammar(vars: Seq[Identifier], maxArity: Int, baseTypes: Seq[TypeTree]) extends ExpressionGrammar {

  def generateProductions(implicit ctx: LeonContext) = {
    val tps@List(a, b, c, d, e, f, g, h) = List("A", "B", "C", "D", "E", "F", "G", "H") map (n => TypeParameter.fresh(n))

    def binary(f: (Expr, Expr) => Expr, tag: Tags.Tag) =
      GenericProdSeed(List(TypeParameterDef(a)), Label(a), List(a, a), map => {
        val label = Label(instantiateType(a, map))
        ProductionRule(
          List(label, label), { case Seq(e1, e2) => f(e1, e2) }, tag, 1, -1.0
        )
      })

    def unary(f: Expr => Expr, tag: Tags.Tag) = {
      val tp = TupleType(Seq(a, a))
      GenericProdSeed(List(TypeParameterDef(a)), Label(tp), List(tp), map => {
        val label = Label(instantiateType(tp, map))
        ProductionRule(
          List(label), { case Seq(e1) => f(e1) }, tag, 1, -1.0
        )
      })
    }

    def cross(l: Int) = {
      val tparams = tps.take(l)
      for (x <- 1 until l) yield {
        val (first, last) = tparams.splitAt(x)
        val subtps = List(flatten(first), flatten(last))
        GenericProdSeed(tparams.map(TypeParameterDef), Label(flatten(tparams)), subtps, map => {
          //println(map)
          val labels = subtps map (tp => Label(instantiateType(tp, map)))

          ProductionRule(
            labels, { case Seq(e1, e2) => Cross(e1, e2) }, RelTags.Cross, 1, -1.0
          )
        })
      }
    }

    def trans =
      GenericProdSeed(List(TypeParameterDef(a), TypeParameterDef(b)), Label(TupleType(Seq(b, a))), List(TupleType(Seq(a, b))), map => {
        val label = Label(instantiateType(TupleType(Seq(a, b)), map))
        ProductionRule(
          List(label), { case Seq(e1) => Transpose(e1) }, RelTags.Transpose, 1, -1.0
        )
      })

    def vr(id: Identifier) = {
      terminal(Label(id.getType), Variable(id), Tags.Top, 1, -1.0)
    }

    def join(l: Int) = {
      val input = tps.take(l)
      val joinTp = tps(l)
      for (x <- 0 to l) yield {
        val first = flatten( (input take x) :+ joinTp)
        val last  = flatten( joinTp +: (input drop x))
        val tps = (input take x) ++ Seq(joinTp) ++ (input drop x)
        GenericProdSeed(tps.map(TypeParameterDef), Label(TupleType(input)), List(first, last), map => {
          val labels = List(first, last) map (tp => Label(instantiateType(tp, map)))
          ProductionRule(
            labels, { case Seq(e1, e2) => Join(e1, e2) }, RelTags.Join, 1, -1.0
          )
        })
      }
    }

    def oneOfTopLevel = {
      def combinations[A](elems: Seq[A], arity: Int): Seq[Seq[A]] = {
        if (arity == 0) Seq(Seq())
        else {
          elems flatMap (elem => combinations(elems, arity - 1) map (elem +: _))
        }
      }

      val allCombos = (1 to maxArity) flatMap (combinations(baseTypes, _))
      allCombos map { tps =>
        val label = Label(flatten(tps))
        nonTerminal(Label(Untyped), Seq(label), { case Seq(x) => x })
      }
    }

    vars.map(vr) ++
    (2 to maxArity).flatMap(cross) ++
    (2 to maxArity).flatMap(join) ++
    List((Union, RelTags.Union), (Inters, RelTags.Inters), (Diff, RelTags.Diff)).map( (binary _).tupled ) ++
    List(RefTransClosure, TransClosure).map(unary(_, RelTags.Closure)) ++
    List(trans) ++
    oneOfTopLevel
  }
}

class Enumerator(grammar: ExpressionGrammar, optimizations: Boolean, rootLabel0: Label) {
  implicit val ctx = LeonContext.empty

  private var cTree: Map[Identifier, Seq[(Identifier, Seq[Expr] => Expr, Seq[Identifier])]] = Map()

  // Top-level C identifiers corresponding to innerP.xs
  private var rootC: Identifier          = _

  // Blockers
  private var bs: Set[Identifier]        = Set()

  // Generator of fresh cs that minimizes labels
  class CGenerator {
    private var buffers = Map[Label, Stream[Identifier]]()

    private var slots = Map[Label, Int]().withDefaultValue(0)

    private def streamOf(t: Label): Stream[Identifier] = Stream.continually(
      FreshIdentifier(t.asString, t.getType, true)
    )

    def rewind(): Unit = {
      slots = Map[Label, Int]().withDefaultValue(0)
    }

    def getNext(t: Label) = {
      if (!(buffers contains t)) {
        buffers += t -> streamOf(t)
      }

      val n = slots(t)
      slots += t -> (n+1)

      buffers(t)(n)
    }
  }

  type Candidate = Set[Identifier]

  private var termSize_ = 0

  def termSize = termSize_


  /**
    * Returns all possible assignments to Bs in order to enumerate all possible programs
    */
  def allCandidates(): Traversable[Candidate] = {

    var cache = Map[Identifier, Seq[Candidate]]()

    def allCandidatesFor(c: Identifier): Seq[Candidate] = {
      if (!(cache contains c)) {
        val subs = for ((b, _, subcs) <- cTree(c)) yield {
          if (subcs.isEmpty) {
            Seq(Set(b))
          } else {
            val subPs = subcs map (s => allCandidatesFor(s))
            val combos = SeqUtils.cartesianProduct(subPs).map(_.flatten.toSet)
            combos map (_ + b)
          }
        }
        cache += c -> subs.flatten
      }
      cache(c)
    }

    allCandidatesFor(rootC)
  }

  // Update the c-tree after an increase in termsize
  def updateCTree(): Unit = {
    //timers.updateCTree.start()
    def freshB() = {
      val id = FreshIdentifier("B", BooleanType, true)
      bs += id
      id
    }

    def defineCTreeFor(l: Label, c: Identifier): Unit = {
      if (!(cTree contains c)) {
        val cGen = new CGenerator()

        val alts = grammar.getProductions(l)

        val cTreeData = alts flatMap { gen =>

          // Optimize labels
          cGen.rewind()

          val subCs = for (sl <- gen.subTrees) yield {
            val subC = cGen.getNext(sl)
            defineCTreeFor(sl, subC)
            subC
          }

          if (subCs.forall(sc => cTree(sc).nonEmpty)) {
            val b = freshB()
            Some((b, gen.builder, subCs))
          } else None
        }

        cTree += c -> cTreeData
      }
    }

    val cGen = new CGenerator()

    def rootLabel = {
      rootLabel0.withAspect(Sized(termSize, optimizations)).withAspect(TypeDepthBound(2))
    }

    rootC = {
      val c = cGen.getNext(rootLabel)
      defineCTreeFor(rootLabel, c)
      c
    }
  }

  def getExpr(bValues: Candidate): Expr = {

    def getCValue(c: Identifier): Expr = {
      cTree(c).find(i => bValues(i._1)).map {
        case (b, builder, cs) =>
          builder(cs.map(getCValue))
      }.getOrElse {
        Error(c.getType, "Impossible assignment of bs")
      }
    }

    getCValue(rootC)
  }

  updateCTree()

  def unfold() = {
    termSize_ += 1
    updateCTree()
  }

  def uptoSize(maxSize: Int) = {
    var exprs = Seq[Expr]()
    for (i <- 1 to maxSize) {
      unfold()
      exprs = Seq() ++ allCandidates().map(getExpr) ++ exprs
    }
    exprs.reverse
  }


}



import Tags.Tag

object RelTags {
  case object Union extends Tag
  case object Inters extends Tag
  case object Diff extends Tag
  case object Transpose extends Tag
  case object Cross extends Tag
  case object Join extends Tag
  case object Closure extends Tag

  val excludedTags = Map[(Tag, Int), Set[Tag]](
    (Union, 0) -> Set(Union, Diff),
    (Union, 1) -> Set(Diff),
    (Inters, 0) -> Set(Inters),
    (Inters, 1) -> Set(),
    (Diff, 0) -> Set(),
    (Diff, 1) -> Set(),
    (Transpose, 0) -> Set(Transpose),
    (Cross, 0) -> Set(),
    (Cross, 1) -> Set(Cross),
    (Join, 0) -> Set(),
    (Join, 1) -> Set(), // FIXME
    (Closure, 0) -> Set(Closure)
  ).withDefaultValue(Set())
}

case class Tagged(tag: Tag, pos: Int) extends Aspect(TaggedAspectKind) {
  import RelTags._

  def asString(implicit ctx: LeonContext): String = s"#$tag@$pos"

  def applyTo(lab: Label, ps: Seq[Production])(implicit ctx: LeonContext) = {
    ps.flatMap { p =>
      val tagsValid = !(excludedTags(tag, pos) contains p.tag)

      if (tagsValid) {
        val newSubs = p.subTrees.zipWithIndex.map { case (lab, pos) =>
          lab.withAspect(Tagged(p.tag, pos))
        }
        Some(p.copy(subTrees = newSubs))
      } else {
        None
      }
    }
  }
}


object RelMain {

  import RelationalAlg._

  implicit val ctx = LeonContext.empty

  def runProblem(ids: Seq[Identifier], maxArity: Int, opNo: Int, opts: Boolean, baseTypes: Seq[TypeTree], rootLabel: Label) = {
    val grammar = new RelationalGrammar(ids, maxArity, baseTypes)
    val enumerator = new Enumerator(grammar, opts, rootLabel)
    val res = enumerator.uptoSize(opNo + 1)
    println(grammar.asString)
    res
  }

  def main(args: Array[String]): Unit = {

    locally {
      val s = FreshIdentifier("s", S)
      val t = FreshIdentifier("t", T)
      val r = FreshIdentifier("r", TupleType(Seq(S, T)))
      val p = FreshIdentifier("r", TupleType(Seq(T, T)))
      val q = FreshIdentifier("r", TupleType(Seq(T, T)))

      val res1 = runProblem(Seq(s,t,r,p,q), 3, 7, false, Seq(S,T), Label(Untyped))
      val res2 = runProblem(Seq(s,t,r,p,q), 3, 7, true , Seq(S,T), Label(Untyped).withAspect(Tagged(Tags.Top, 0)))

      println("------ 1 ----------")
      //res1 foreach println
      println("------ 2 ----------")
      //res2 foreach println
      println(s"Size 1: ${res1.size}")
      println(s"Size 2: ${res2.size}")
    }

  }
}