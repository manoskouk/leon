/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Common._
import Trees._
import TypeTrees._
import Definitions._
import Constructors._

import PrinterHelpers._

/** This pretty-printer only print valid scala syntax */
class ScalaPrinter(opts: PrinterOptions, sb: StringBuffer = new StringBuffer) extends PrettyPrinter(opts, sb) {
  import Common._
  import Trees._
  import TypeTrees._
  import Definitions._

  import java.lang.StringBuffer

  override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
   
    tree match {
      case Not(Equals(l, r))    => p"$l != $r"
      case Implies(l,r)         => pp(or(not(l), r))
      case Choose(vars, pred, None) => p"choose((${typed(vars)}) => $pred)"
      case s @ FiniteSet(rss)    => {
        val rs = rss.toSeq
        s.getType match {
          case SetType(ut) =>
            p"Set[$ut]($rs)"
          case _ =>
            p"Set($rs)"
        }
      }
      case m @ FiniteMap(els) => {
        m.getType match {
          case MapType(k,v) =>
            p"Map[$k,$v]($els)"
          case _ =>
            p"Map($els)"
        }
      }
      case ElementOfSet(e,s)    => p"$s.contains(e)"
      case SetUnion(l,r)        => p"$l ++ $r"
      case MapUnion(l,r)        => p"$l ++ $r"
      case SetDifference(l,r)   => p"$l -- $r"
      case SetIntersection(l,r) => p"$l & $r"
      case SetCardinality(s)    => p"$s.size"
      case FiniteArray(exprs)   => p"Array($exprs)"
      case Not(expr)            => p"!$expr"
      case _ =>
        super.pp(tree)
    }
  }
}

object ScalaPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions) = new ScalaPrinter(opts)
}
