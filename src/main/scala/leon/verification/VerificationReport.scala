/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._

class VerificationReport(val program : Program, val fvcs: Map[FunDef, List[VerificationCondition]]) {
  val conditions : Seq[VerificationCondition] = fvcs.flatMap(_._2).toSeq.sortWith {
      (vc1,vc2) =>
        val id1 = vc1.funDef.id.name
        val id2 = vc2.funDef.id.name
        if(id1 != id2) id1 < id2 else vc1.getPos < vc2.getPos
    }

  lazy val totalConditions : Int = conditions.size

  lazy val totalTime : Double = conditions.foldLeft(0.0d)((t,c) => t + c.time.getOrElse(0.0d))

  lazy val totalValid : Int = conditions.count(_.value == Some(true))

  lazy val totalInvalid : Int = conditions.count(_.value == Some(false))

  lazy val totalUnknown : Int = conditions.count(_.value == None)

  def summaryString : String = if(totalConditions >= 0) {
    VerificationReport.infoHeader +
    conditions.map(VerificationReport.infoLine).mkString("\n", "\n", "\n") +
    VerificationReport.infoSep +
    ("║ total: %-4d   valid: %-4d   invalid: %-4d   unknown %-4d " +
      (" " * 21) +
      " %7.3f ║\n").format(totalConditions, totalValid, totalInvalid, totalUnknown, totalTime) +
    VerificationReport.infoFooter
  } else {
    "No verification conditions were analyzed."
  }
}

object VerificationReport {
  def emptyReport(p:Program) : VerificationReport = new VerificationReport(p,Map())

  private def fit(str : String, maxLength : Int) : String = {
    if(str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private val infoSep    : String = "╟" + ("┄" * 88) + "╢\n"
  private val infoFooter : String = "╚" + ("═" * 88) + "╝"
  private val infoHeader : String = ". ┌─────────┐\n" +
                                    "╔═╡ Summary ╞" + ("═" * 76) + "╗\n" +
                                    "║ └─────────┘" + (" " * 76) + "║"

  private def infoLine(vc : VerificationCondition) : String = {
    val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")

    "║ %-25s %-9s %14s %-8s %-10s %-7s %7s ║".format(
      fit(vc.funDef.id.toString, 25),
      vc.kind,
      vc.getPos,
      vc.status,
      vc.tacticStr,
      vc.solverStr,
      timeStr)
  }
}
