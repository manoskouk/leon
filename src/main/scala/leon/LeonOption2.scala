/* Copyright 2009-2014 EPFL, Lausanne */

package leon.duh

sealed abstract class LeonOptionDef[A] {
  type T = A
  val name: String
  val defaultValue: A
  val usageDesc: String
  val usageOption: String
  def printWithValue(v: A): String
  def default = LeonOption(this, defaultValue)
  def parseValue(s: String): A
}

class LeonFlagOptionDef(val name: String, val defaultValue: Boolean, val usageDesc: String) extends LeonOptionDef[Boolean] {
  val usageOption = "--" + name //+ (if (defaultValue) "=off" else "")
  def printWithValue(v: Boolean) = "--" + name + (if (v) "=off" else "")
  def parseValue(s: String) = s match {
    case "true"  | "on"  | "yes" | "" => true
    case "false" | "off" | "no"       => false
    case _ => ???
  }
}

abstract class LeonValueOptionDef[A] extends LeonOptionDef[A] {
  val example: String
  val usageOption = s"--$name=$example"
  def printWithValue(v: A) = s"--$name=$v"
}

abstract class LeonStringOptionDef(val name: String, val defaultValue: String, val example: String, val usageDesc: String) extends LeonValueOptionDef[String] {
  def parseValue(v: String) = v
}

sealed abstract class LeonSeqOptionDef[A](val name: String, val example: String, val usageDesc: String)
    extends LeonValueOptionDef[Seq[A]]{
  val defaultValue = Seq()
  override def printWithValue(v: Seq[A]) = "--" + name + "=" + (v mkString ",")
  def parseValue(s: String) = ???
}


object OptionUseStuff extends LeonFlagOptionDef("useStuff", true, "Enable awesome stuff") 
object OptionFunctions extends LeonSeqOptionDef[String]("functions", "f1,f2,...", "Constrain analysis to f1,f2,...")



case class LeonOption[A](optionDef: LeonOptionDef[A], value: A) {
  override def toString = optionDef.printWithValue(value)
}


object LeonOption {
  private val leonOptionFormat = "--([^=]+)(=(.+))?".r
  def parse(s: String)(implicit knownDefs: Set[LeonOptionDef[Any]]): Option[LeonOption[_]] = {
    s match {
      case leonOptionFormat(name, _, value) =>
        knownDefs find { _.name == name } map { df =>
          LeonOption(df, df.parseValue(Option(value) getOrElse ""))
        }
      case _ => None
    }
  }
}



/*
object Parsers {


  

  def apply[A](s: String)(implicit available: Set[LeonOption[A]], parser: Parser[A]): Option[LeonOption[A]] = {
    
  }

  private def parse
*/
