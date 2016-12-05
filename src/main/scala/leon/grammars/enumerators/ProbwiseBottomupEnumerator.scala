/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package enumerators

import purescala.Common.Identifier
import purescala.Definitions.Program
import purescala.Expressions.Expr
import evaluators.TableEvaluator
import synthesis.Example
import scala.annotation.tailrec
import scala.collection.{mutable => mut}

/** An enumerator that jointly enumerates elements from a number of production rules by employing a bottom-up strategy.
  * After initialization, each nonterminal will produce a series of unique elements in decreasing probability order.
  *
  * @param nts A mapping from each nonterminal to the production rules corresponding to it,
  *            and the rule which corresponds to the first element
  * @tparam NT Type of the nonterminal of the production rules.
  * @tparam R The type of enumerated elements.
  */
abstract class AbstractProbwiseBottomupEnumerator[NT, R](nts: Map[NT, (ProductionRule[NT, R], Seq[ProductionRule[NT, R]])]){

  protected val ctx: LeonContext
  protected type Rule = ProductionRule[NT, R]
  protected type Coords = Seq[Int]

  protected val timers = ctx.timers.synthesis.applications.get("Prob-Enum")

  protected type Sig
  protected def mkSig(elem: StreamElem): Sig

  protected case class StreamElem(rule: Rule, subs: Seq[StreamElem]){
    val r: R = rule.builder(subs map (_.r))
    val logProb: Double = subs.map(_.logProb).sum + rule.weight
    lazy val sig = mkSig(this)
  }

  protected val applyTagOpt = true
  protected val budget = -500.0
  protected def isDistinct(elem: StreamElem, previous: mut.HashSet[Sig]): Boolean

  trait TryNext[+A] {
    def map[B](f: A => B): TryNext[B] = this match {
      case Success(e) => Success(f(e))
      case other => other.asInstanceOf[TryNext[B]]
    }
    def get: A = throw new UnsupportedOperationException("TryNext.get")
    def isSuccess = false
  }
  case class Success[A](e: A) extends TryNext[A] {
    override def get = e
    override def isSuccess = true
  }
  case object Depleted extends TryNext[Nothing]
  case object Suspended extends TryNext[Nothing]

  def tnOrdering[A](implicit sub: Ordering[A]) = new Ordering[TryNext[A]] {
    def compare(x: TryNext[A], y: TryNext[A]): Int = (x, y) match {
      case (Success(elem1), Success(elem2)) => sub.compare(elem1, elem2)
      case (Success(_), _) => 1
      case (_, Success(_)) => -1
      case (Depleted,  Suspended) => -1
      case (Suspended, Depleted ) => 1
      case _ => 0
    }
  }


  // Represents the frontier of an operator, i.e. a set of the most probable combinations of operand indexes
  // such that each other combination that has not been generated yet has an index >= than one element of the frontier
  // Stores the elements in a priority queue by maximum probability
  class Frontier(dim: Int, rule: Rule, streams: Seq[NonTerminalStream]) {
    private val ordering = Ordering.by[FrontierElem, Double](_.streamElem.logProb)
    private val queue = new mut.PriorityQueue[FrontierElem]()(ordering)
    private var futureElems = List.empty[FutureElem]

    private val byDim = Array.fill(dim)(
     mut.HashMap[Int, mut.HashSet[FrontierElem]]()
        .withDefaultValue(mut.HashSet[FrontierElem]())
    )

    @inline private def dominates(e1: FrontierElem, e2: FrontierElem) =
      e1.coordinates zip e2.coordinates forall ((_: Int) <= (_: Int)).tupled

    @inline private def enqueue(elem: FrontierElem, grownDim: Int) = {
      val approved = grownDim < 0 || {
        val grownTo = elem.coordinates(grownDim)
        val elems = byDim(grownDim)(grownTo)
        !(elems exists (dominates(_, elem)))
      }
      if (approved) {
        queue += elem
        for (i <- 0 until dim) {
          val coord = elem.coordinates(i)
          byDim(i)(coord) += elem
        }
      }
    }

    // Add an element suspension to the frontier
    @inline def +=(l: FutureElem) = {
      futureElems ::= l
    }

    // Calculate an element from a suspension by retrieving elements from the respective nonterminal streams
    @inline private def elem(le: FutureElem): TryNext[(FrontierElem, Int)] = {
      val children = le.coordinates.zip(streams).map { case (index, stream) => stream.get(index) }
      if (children contains Depleted) Depleted
      else if (children contains Suspended) Suspended
      else {
        val operands = children.map(_.get)
        if (applyTagOpt && operands.map(_.rule.tag).zipWithIndex.exists { case (t, ind) =>
          Tags.excludedTags((rule.tag, ind)) contains t
        })
          Depleted
        else {
          val se = StreamElem(rule, operands)
          if (se.logProb >= budget)
            Success(FrontierElem(le.coordinates, se), le.grownIndex)
          else Depleted
        }
      }
    }

    // promote all elements suspensions to frontier elements
    private def promote() = {
      def filter(fe: FutureElem) = elem(fe) match {
        case Depleted => false
        case Suspended => true
        case Success((elem, index)) =>
          enqueue(elem, index)
          false
      }

      futureElems = futureElems.reverse.filter(filter).reverse
      // if (dim > 0) println(f"dim: $dim: 0: ${byDim(0)(0).map(_.coordinates(0)).max}%5d #: ${queue.size}%3d")
    }

    // This should only be called after tryHead!
    def dequeue() = {
      assume(queue.nonEmpty)
      val res = queue.dequeue()
      for (i <- 0 until dim)
        byDim(i)(res.coordinates(i)) -= res
      res
    }

    def tryHead: TryNext[FrontierElem] = {
      promote()
      queue.headOption match {
        case Some(elem) => Success(elem)
        case None =>
          if (futureElems.isEmpty) Depleted else Suspended
      }
    }

    // This should only be called after tryHead!
    @inline def isEmpty = queue.isEmpty
  }

  /** A suspension of a frontier element (which has not yet retrieved its operands) */
  protected case class FutureElem(coordinates: List[Int], grownIndex: Int)

  /** An element of the frontier */
  protected case class FrontierElem(coordinates: List[Int], streamElem: StreamElem) {
    def nextElems = coordinates.zipWithIndex.map {
      case (elem, updated) => FutureElem(coordinates.updated(updated, elem + 1), updated)
    }
  }

  // The streams of elements corresponding to each nonterminal
  protected val streams: Map[NT, NonTerminalStream] =
    nts.map{ case (nt, _) => (nt, new NonTerminalStream(nt)) }

  // The operator streams per nonterminal
  protected val operators: Map[NT, Seq[OperatorStream]] =
    nts.map { case (nt, (advanced, prods)) =>
      nt -> prods.map(rule => new OperatorStream(rule, rule eq advanced))
    }

  /** A class that represents the stream of generated elements for a specific nonterminal. */
  protected class NonTerminalStream(nt: NT) extends Iterable[R] {

    protected val buffer: mut.ArrayBuffer[StreamElem] = new mut.ArrayBuffer()
    protected val hashSet: mut.HashSet[Sig] = new mut.HashSet()

    // The first element to be produced will be the one recursively computed by the horizon map.
    private def initialize(): Unit = {
      def rec(nt: NT): StreamElem = {
        val rule = nts(nt)._1
        StreamElem(rule, rule.subTrees.map(rec))
      }
      val elem = rec(nt)
      isDistinct(elem, hashSet)
      buffer += elem
    }

    initialize()

    private var lock = false
    private var depleted = false

    val pairOrd = new Ordering[(StreamElem, OperatorStream)] {
      def compare(x: (StreamElem, OperatorStream), y: (StreamElem, OperatorStream)): Int = {
        val doubleOrd = implicitly[Ordering[Double]]
        doubleOrd.compare(x._1.logProb, y._1.logProb)
      }
    }

    implicit val ord = tnOrdering(pairOrd)

    // Add a new element to the buffer
    private def populateNext() = {
      if (depleted) Depleted
      else if (lock) Suspended
      else {
        lock = true
        @tailrec def rec: TryNext[StreamElem] = {
          //println(s"$nt: size is ${buffer.size}, populating")
          operators(nt).map(_.getNext).max match {
            case Success((elem, op)) =>
              op.advance()
              if (isDistinct(elem, hashSet)) {
                buffer += elem
                Success(elem)
              } else rec
            case Suspended =>
              Suspended
            case Depleted =>
              depleted = true
              Depleted
            //println(s"$nt: Adding ($r, $d)")
          }
        }
        val res = rec
        lock = false
        res
      }
    }

    // Get the i-th element of the buffer
    @inline def get(i: Int): TryNext[StreamElem] = {
      if (i == buffer.size) populateNext()
      else if (i > buffer.size) sys.error("Whoot?")
      else Success(buffer(i))
    }

    def iterator: Iterator[R] = new Iterator[R] {
      var i = 0
      def hasNext = get(i).isSuccess
      def next = {
        val res = get(i).get.r
        i += 1
        res
      }
    }

  }

  /** Generates elements for a specific operator */
  protected class OperatorStream(rule: ProductionRule[NT, R], isAdvanced: Boolean) {
    private val arity = rule.arity
    private val typedStreams = rule.subTrees.map(streams)
    private val frontier: Frontier = new Frontier(arity, rule, typedStreams)

    @inline def getNext: TryNext[(StreamElem, OperatorStream)] = {
      frontier.tryHead.map(fe => (fe.streamElem, this))
    }

    // Remove the top element of the frontier and add its derivatives
    def advance(): Unit = if (!frontier.isEmpty) {
      frontier.dequeue().nextElems foreach { frontier += _ }
    }

    private def init(): Unit = {
      frontier += FutureElem(List.fill(arity)(0), -1)
      if (isAdvanced) advance()
    }
    init()
  }

  def iterator(nt: NT) = streams.get(nt).map(_.iterator).getOrElse(Iterator())
}

class ProbwiseBottomupEnumerator(protected val grammar: ExpressionGrammar, init: Label)(implicit protected val ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator[Label, Expr](ProbwiseBottomupEnumerator.productive(grammar, init))
  with GrammarEnumerator
{
  type Sig = Unit
  @inline protected def isDistinct(elem: StreamElem, previous: mut.HashSet[Sig]): Boolean = true
  @inline protected def mkSig(elem: StreamElem): Sig = ()
}


class EqClassesEnumerator( protected val grammar: ExpressionGrammar,
                           init: Label,
                           as: Seq[Identifier],
                           examples: Seq[Example],
                           program: Program
                         )(implicit protected val ctx: LeonContext)
  extends AbstractProbwiseBottomupEnumerator(ProbwiseBottomupEnumerator.productive(grammar, init))
  with GrammarEnumerator
{
  protected lazy val evaluator = new TableEvaluator(ctx, program)
  protected type Sig = Option[Seq[Expr]]

  protected def mkSig(elem: StreamElem): Sig = {
    import elem._

    def evalEx(subs: Seq[Expr], ex: Example) = {
      evaluator.eval(rule.builder(subs), as.zip(ex.ins).toMap).result
    }
    val res = if (subs.isEmpty) {
      examples.mapM(evalEx(Nil, _))
    } else {
      for {
        subSigs0 <- subs mapM (_.sig)
        subSigs = subSigs0.transpose
        res <- subSigs zip examples mapM (evalEx _).tupled
      } yield res
    }
    res
  }

  protected def isDistinct(elem: StreamElem, previous: mut.HashSet[Sig]): Boolean = {
    previous.add(elem.sig)
  }

}

object ProbwiseBottomupEnumerator {
  import GrammarEnumerator._
  def productive(grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext) = {
    val ntMap = horizonMap(init, grammar.getProductions).collect {
      case (l, (Some(r), _)) => l -> (r, grammar.getProductions(l))
    }
    ntMap.map{ case (k, (r, prods)) => k -> (r, prods.filter(_.subTrees forall ntMap.contains)) }
  }
}
