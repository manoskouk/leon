package leon
package synthesis
package utils

import bonsai._

import Helpers._

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.DefOps._
import purescala.TypeTreeOps._
import purescala.Extractors._
import purescala.ScalaPrinter

import scala.collection.mutable.{HashMap => MutableMap}

class ExpressionGrammar(ctx: LeonContext, prog: Program, inputs: Seq[Expr], currentFunction: FunDef, pathCondition: Expr) {
  def this(sctx: SynthesisContext, p: Problem) = {
    this(sctx.context, sctx.program, p.as.map(_.toVariable), sctx.functionContext, p.pc)
  }

  type Gen = Generator[TypeTree, Expr]

  private[this] val cache = new MutableMap[TypeTree, Seq[Gen]]()

  def getGenerators(t: TypeTree): Seq[Gen] = {
    cache.getOrElse(t, {
      val res = computeGenerators(t)
      cache += t -> res
      res
    })
  }

  def computeGenerators(t: TypeTree): Seq[Gen] = {
    computeBaseGenerators(t) ++
    computeInputGenerators(t) ++
    computeFcallGenerators(t) ++
    computeSafeRecCalls(t)
  }

  def computeBaseGenerators(t: TypeTree): Seq[Gen] = t match {
    case BooleanType =>
      List(
        Generator(Nil, { _ => BooleanLiteral(true) }),
        Generator(Nil, { _ => BooleanLiteral(false) })
      )
    case Int32Type =>
      List(
        Generator(Nil, { _ => IntLiteral(0) }),
        Generator(Nil, { _ => IntLiteral(1) }),
        Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Plus(a, b) }),
        Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Minus(a, b) }),
        Generator(List(Int32Type, Int32Type), { case Seq(a,b) => Times(a, b) })
      )
    case TupleType(stps) =>
      List(Generator(stps, { sub => Tuple(sub) }))

    case cct: CaseClassType =>
      List(
        Generator(cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
      )

    case act: AbstractClassType =>
      act.knownCCDescendents.map { cct =>
        Generator[TypeTree, Expr](cct.fields.map(_.getType), { case rs => CaseClass(cct, rs)} )
      }

    case st @ SetType(base) =>
      List(
        Generator(List(base),   { case elems     => FiniteSet(elems.toSet).setType(st) }),
        Generator(List(st, st), { case Seq(a, b) => SetUnion(a, b) }),
        Generator(List(st, st), { case Seq(a, b) => SetIntersection(a, b) }),
        Generator(List(st, st), { case Seq(a, b) => SetDifference(a, b) })
      )

    case _ =>
      Nil
  }

  def computeInputGenerators(t: TypeTree): Seq[Gen] = {
    inputs.collect {
      case i if isSubtypeOf(i.getType, t) => Generator[TypeTree, Expr](Nil, { _ => i })
    }
  }

  def computeFcallGenerators(t: TypeTree): Seq[Gen] = {

    def getCandidates(fd: FunDef): Seq[TypedFunDef] = {
      // Prevents recursive calls
      val cfd = currentFunction

      val isRecursiveCall = (prog.callGraph.transitiveCallers(cfd) + cfd) contains fd

      val isNotSynthesizable = fd.body match {
        case Some(b) =>
          !containsChoose(b)

        case None =>
          false
      }


      if (!isRecursiveCall && isNotSynthesizable) {
        val free = fd.tparams.map(_.tp)
        canBeSubtypeOf(fd.returnType, free, t) match {
          case Some(tpsMap) =>
            val tfd = fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp)))

            if (tpsMap.size < free.size) {
              /* Some type params remain free, we want to assign them:
               *
               * List[T] => Int, for instance, will be found when
               * requesting Int, but we need to assign T to viable
               * types. For that we use problem inputs as heuristic,
               * and look for instantiations of T such that input <?:
               * List[T].
               */
              inputs.map(_.getType).distinct.flatMap { (atpe: TypeTree) =>
                var finalFree = free.toSet -- tpsMap.keySet
                var finalMap = tpsMap

                for (ptpe <- tfd.params.map(_.tpe).distinct) {
                  canBeSubtypeOf(atpe, finalFree.toSeq, ptpe) match {
                    case Some(ntpsMap) =>
                      finalFree --= ntpsMap.keySet
                      finalMap  ++= ntpsMap
                    case _ =>
                  }
                }

                if (finalFree.isEmpty) {
                  List(fd.typed(free.map(tp => finalMap.getOrElse(tp, tp))))
                } else {
                  Nil
                }
              }
            } else {
              /* All type parameters that used to be free are assigned
               */
              List(tfd)
            }
          case None =>
            Nil
        }
      } else {
        Nil
      }
    }

    val funcs = functionsAvailable(prog).toSeq.flatMap(getCandidates)

    funcs.map{ tfd =>
      Generator[TypeTree, Expr](tfd.params.map(_.tpe), { sub => FunctionInvocation(tfd, sub) })
    }
  }

  def computeSafeRecCalls(t: TypeTree): Seq[Gen] = {
    val calls = terminatingCalls(prog, t, pathCondition)

    calls.map {
      case (e, free) =>
        val freeSeq = free.toSeq
        Generator[TypeTree, Expr](freeSeq.map(_.getType), { sub =>
          replaceFromIDs(freeSeq.zip(sub).toMap, e)
        })
    }
  }

  def computeSubexpressionGenerators(canPlacehold : Expr => Boolean)(e : Expr) : Seq[Gen] = {

    /** A simple Generator API **/

    def gen(tps : Seq[TypeTree], f : Seq[Expr] => Expr) : Gen = 
      Generator[TypeTree, Expr](tps,f)

    // A generator that accepts a single type, and always regenerates its input
    // (simple placeholder of 1 position)
    def wildcardGen(tp : TypeTree) = gen(Seq(tp), { case Seq(x) => x })

    // A generator that always regenerates its input
    def const(e: Expr) : Gen = gen(Seq(), _ => e)
 
    // Creates a new generator by applying f on the result of g.builder
    def map(f : Expr => Expr)(g : Gen) : Gen = {
      gen(g.subTrees, es => f(g.builder(es)) )
    }

    // Concatenate a sequence of generators into a generator.
    // The arity of the resulting generator is the total arity of the constituting generators.
    // builder is the function combining the results of the partial generators
    def concat(gens : Seq[Gen], builder : Seq[Expr] => Expr ) : Gen = {
      val types = gens flatMap { _.subTrees }
      gen(
        types,
        exprs => {
          assert(exprs.length == types.length) // Total arity is arity of subgenerators
          var remaining = exprs
          val fromSubGens = for (gen <- gens) yield {
            val (current, rem) = remaining splitAt gen.arity
            remaining = rem
            gen.builder(current)
          }
          builder(fromSubGens)
        }
      )
          
    }

    
    def rec(e : Expr) : Seq[Gen] = {
      
      // Add an additional wildcard generator, if current expression passes the filter
      def optWild(gens : Seq[Gen]) : Seq[Gen] = 
        if (canPlacehold(e)) {
           wildcardGen(e.getType) +: gens
        }
        else gens


      e match {

        case t : Terminal => 
          // In case of Terminal, we either return the terminal itself, or the input expression
          optWild(Seq(const(t)))
          
        case UnaryOperator(sub, builder) =>
          val fromSub = for (subGen <- rec(sub)) yield map(builder)(subGen) 
          optWild(fromSub)

        case BinaryOperator(e1,e2,builder) =>
          val fromSub = for {
            subGen1 <- rec(e1)
            subGen2 <- rec(e2)
          } yield concat(Seq(subGen1, subGen2), { case Seq(e1,e2) => builder(e1,e2) })

          optWild(fromSub)

        case NAryOperator(subExpressions, builder) =>

          def combinations[A](seqs : Seq[Seq[A]]) : Seq[Seq[A]] = {
            if (seqs.isEmpty) Seq(Seq())
            else for {
              hd <- seqs.head
              tl <- combinations(seqs.tail)
            } yield hd +: tl
          }

          val combos = combinations(subExpressions map rec) 
          val fromSub = combos map { concat(_, builder) }
     
          optWild(fromSub)
      }
    }
    
    rec(e)

  }

  def computeCompleteSubexpressionGenerators = inputs flatMap computeSubexpressionGenerators{ _ => true}


  def printGrammar(printer: String => Unit) {
    for ((t, gs) <- cache; g <- gs) {
      val subs = g.subTrees.map { tpe => FreshIdentifier(tpe.toString).setType(tpe).toVariable }
      val gen = g.builder(subs)

      printer(f"$t%30s ::= "+gen)
    }
  }
}
