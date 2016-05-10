/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.DefOps._
import purescala.Expressions._
import purescala.TypeOps.canBeSubtypeOf
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Extractors._
import leon.solvers._
import leon.utils.Simplifiers

case object Abduction extends Rule("Abduction") {
  override def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // Let ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧ be the original problem
    // and replacedXs some subset of xs.
    // We will abduce replacedXs <- tfd(newXs), newXs fresh, and remove replacedXs
    def processFd(replacedXs: Seq[Identifier], tfd: TypedFunDef): Option[RuleInstantiation] = {

      import hctx.reporter.debug

      // We assign replacedXs = tfd(extraXs), extraXs fresh
      val extraXs = tfd.paramIds map (_.duplicate(alwaysShowUniqueID = true))
      val args  = extraXs map Variable
      val call  = FunctionInvocation(tfd, args)
      val replacedTuple = tupleWrap(replacedXs map Variable)

      debug(s"Will try replacing $replacedTuple <- $call")

      // prec. of tfd(extraXs) (extraXs have to satisfy it)
      val pre = replaceFromIDs(tfd.paramIds.zip(args).toMap, tfd.precOrTrue)

      // Fail if pre is not SAT
      val solver = SimpleSolverAPI(SolverFactory.getFromSettings(hctx, hctx.program).withTimeout(1000))
      if (!solver.solveSAT(p.pc implies pre)._1.contains(true)){
        debug(s"Prec. of $call UNSAT! No point trying!")
        return None
      }

      // postc. of tfd(extraXs) will hold for xs
      val post = simplifyLets(application(
        replaceFromIDs(tfd.paramIds.zip(args).toMap, tfd.postOrTrue),
        Seq(replacedTuple)
      ))

      // Conceptually, the new problem is
      // ⟦ as ⟨ ws && pc && xs <- tfd(extraXs) && post | pre && phi ⟩ extraXs ⟧
      // But we will only accept this problem if xs is simplifiable in phi under the new assumptions

      def containsXs(e: Expr) = (variablesOf(e) & replacedXs.toSet).nonEmpty

      val newPhi = {

        val newPhi0 = {
          // Try to eliminate xs in trivial cases
          val TopLevelAnds(newPhis) = and(pre, post)
          val equalities = newPhis.collect {
            case Equals(e1, e2) if containsXs(e1) && !containsXs(e2) => e1 -> e2
            case Equals(e1, e2) if containsXs(e2) && !containsXs(e1) => e2 -> e1
          }.toMap

          replace(equalities, p.phi)
        }

        val bigX = FreshIdentifier("x", call.getType, alwaysShowUniqueID = true)

        val projections = replacedXs.indices map { ind =>
          tupleSelect(Variable(bigX), ind + 1, replacedXs.size)
        }

        val pc = p.pc
          .withCond(pre)
          .withBinding(bigX, call)
          .withBindings(replacedXs zip projections)
          .withCond(post)

        //println(pc)
        //println(newPhi0)

        Simplifiers.bestEffort(hctx, hctx.program)(newPhi0, pc)
      }

      // Ugly, but we need to debug...
      val rejectMsg = {
        if      (containsXs(newPhi)) Some(s"$newPhi contains one of $replacedXs")
        else if (canBeHomomorphic(p.phi, newPhi).isDefined) Some(s"${p.phi} and $newPhi are homomorphic")
        else None
      }

      rejectMsg match {
        case Some(msg) =>
          debug(msg)
          None
        case None =>
          // We do not need xs anymore, so we accept the decomposition.
          // We can remove xs-related clauses from the PC.
          // Notice however we need to synthesize extraXs such that pre is satisfied as well.
          // Final problem is:
          // ⟦ as ⟨ ws && pc | pre && phi ⟩ extraXs ⟧
          val newXs = p.xs.diff(replacedXs) ++ extraXs

          val newP = p.copy(phi = and(pre, newPhi), xs = newXs) // FIXME InOutExamples

          // This needs some clarification:
          // Let's say
          //   original problem had xs = (x1, x2, x3),
          //   call replaces (x2, x3) and introduces (x4, x5, x6),
          //   and the subproblem returned 'e'.
          // Then we need to return
          //   val (x1, x4, x5, x6) = e
          //   val (x2, x3) = call(x4, x5, x6)
          //   (x1, x2, x3)
          val onSuccess: List[Solution] => Option[Solution] = {
            val freshIds = ( p.xs map (id => id -> id.duplicate(alwaysShowUniqueID = true))).toMap.withDefault(id => id)
            def freshen(ids: Seq[Identifier]) = ids map freshIds
            l => {
              val List(Solution(pre, defs, term, isTrusted)) = l
              val newTerm = {
                letTuple(freshen(newXs), term,
                  letTuple(freshen(replacedXs), call,
                    tupleWrap(freshen(p.xs).map(Variable))
                  )
                )
              }
              Some(Solution(pre, defs, newTerm, isTrusted))
            }
          }

          Some(decomp(List(newP), onSuccess, s"Abduce $replacedTuple <- $call"))
        }
    }

    // A list of function -> arg that exist in current partial solution.
    // We want to avoid v1 <- f(v2) and then v2 <- f(v3)
    val prevCalls = {
      val placeHolder = Variable(FreshIdentifier("xs", p.outType))

      val soFar = new PartialSolution(hctx.search.strat, includeUntrusted = false)
        .solutionAround(hctx.currentNode)(placeHolder).get.toExpr

      val calls = functionCallsOf(soFar).toSeq.map {
        case FunctionInvocation(TypedFunDef(fd, _), args) =>
          fd -> args
      }

      val topLevelCall = hctx.functionContext -> hctx.search.p.xs.map(Variable)

      (calls :+ topLevelCall)
        .groupBy(_._1)
        .mapValues( argss => argss.flatMap(_._2).toSet)
        .withDefaultValue(Set())
    }
    //prevCalls foreach { case (f, as) =>
    //  println(s"${f.id} -> $as")
    //}

    val filterOut = (fd: FunDef) => fd.isSynthetic || fd.isInner

    val funcs = visibleFunDefsFromMain(hctx.program).toSeq.sortBy(_.id).filterNot(filterOut)

    def retTypeCompatible(fd: FunDef, xs: Seq[Identifier]) = {
      canBeSubtypeOf(fd.returnType, tupleTypeWrap(xs map (_.getType)))
    }

    for {
      fd      <- funcs
      // For now it is either one variable or all variables
      xsCombo <- if (p.xs.size == 1) Seq(p.xs) else p.xs.map(Seq(_)) :+ p.xs
      inst    <- retTypeCompatible(fd, xsCombo)
      // We want to avoid v1 <- f(v2) and then v2 <- f(v3)
      if (prevCalls(fd) & xsCombo.map(Variable).toSet).isEmpty
      decomp  <- processFd(xsCombo, fd.typed(fd.tparams map (tpar => inst(tpar.tp))))
    } yield decomp

  }
}
