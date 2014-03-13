package leon.purescala

import leon._
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.Trees._
import leon.purescala.TreeOps.preMapOnFunDef
import leon.purescala.TypeTrees._

object RestoreMethods extends TransformationPhase {
  
  val name = "Restore methods"
  val description = "Restore methods that were previously turned into standalone functions"
    
  /**
   * New functions are returned, whereas classes are mutated
   */
  def apply(ctx : LeonContext, p : Program) = {
        
    var fd2Md = Map[FunDef, FunDef]()
    var whoseMethods = Map[ClassDef, Seq[FunDef]]()
    
    /**
     * Substitute a "this$" identifier with "this" keyword
     */
    def this2This(e : Expr) = e match {
      case Variable(thisId : ThisIdentifier) => Some(This(thisId.cType))
      case _ => None
    }
    
    for ( (Some(cd : ClassDef), funDefs) <- p.definedFunctions.groupBy(_.enclosing).toSeq ) {
      whoseMethods += cd -> funDefs
      for (fn <- funDefs) {
        val namePieces = fn.id.name.split("\\$",2) // name without enclosing class appended
        val theName = if (namePieces(0) == cd.id.name && namePieces.length > 1){ 
          // <className>$ has indeed been added 
          namePieces(1)
        } else { 
          // otherwise keep the same name
          fn.id.name
        }
        val md = fn.copy(
          id = FreshIdentifier(theName), 
          params = fn.params.tail, // no this$
          tparams = fn.tparams diff cd.tparams 
        ).copiedFrom(fn)
        md.copyContentFrom(fn)
        val mdFinal = preMapOnFunDef(this2This)(md)
        fd2Md += fn -> mdFinal       
      }
    } 
     
    /**
     * Substitute a function in an expression with the respective new method
     * Used as an argument for preMap
     */
    def substituteMethods = preMapOnFunDef ({
      case FunctionInvocation(tfd,args) if fd2Md contains tfd.fd => {
        val md = fd2Md.get(tfd.fd).get // the method we are substituting
        val mi = MethodInvocation(
          args.head, // "this"
          args.head.getType.asInstanceOf[ClassType].classDef, // this.type
          md.typed(tfd.tps.takeRight(md.tparams.length)),  // throw away class parameters
          args.tail // rest of the arguments
        )
        Some(mi)
      }
      case _ => None
    }, true) _
    
    /**
     * Renew that function map by applying subsituteMethods on its values to obtain correct functions
     */
    val fd2MdFinal = fd2Md.mapValues(substituteMethods)
    
    
    p.copy(modules = p.modules map { m =>
      val newFuns : Seq[FunDef] = m.definedFunctions diff fd2MdFinal.keys.toSeq map substituteMethods// only keep non-methods
      for (
        cl <- m.definedClasses;
        fun <- whoseMethods.get(cl).getOrElse(Seq()) // Seq() (or no methods) for a class that has none
      ) { cl.registerMethod(fd2MdFinal.get(fun).getOrElse(scala.sys.error("Function absent from map???"))) }
      m.copy(defs = m.definedClasses ++ newFuns).copiedFrom(m)
    })
    
  }

} 