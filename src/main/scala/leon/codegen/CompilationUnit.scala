/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor

import CodeGeneration._

class CompilationUnit(val program: Program, val classes: Map[Definition, ClassFile], implicit val env: CompilationEnvironment) {

  val jvmClassToDef = classes.map {
    case (d, cf) => cf.className -> d
  }.toMap

  protected[codegen] val loader = {
    val l = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)
    classes.values.foreach(l.register(_))
    l
  }

  private val caseClassConstructors : Map[CaseClassDef,Constructor[_]] = {
    (classes collect {
      case (ccd : CaseClassDef, cf) =>
        val klass = loader.loadClass(cf.className)
        // This is a hack: we pick the constructor with the most arguments.
        val conss = klass.getConstructors().sortBy(_.getParameterTypes().length)
        assert(!conss.isEmpty)
        (ccd -> conss.last)
    }).toMap
  }

  private lazy val tupleConstructor: Constructor[_] = {
    val tc = loader.loadClass("leon.codegen.runtime.Tuple")
    val conss = tc.getConstructors().sortBy(_.getParameterTypes().length)
    assert(!conss.isEmpty)
    conss.last
  }

  private def writeClassFiles() {
    for ((d, cl) <- classes) {
      cl.writeToFile(cl.className + ".class")
    }
  }

  private var _nextExprId = 0
  private def nextExprId = {
    _nextExprId += 1
    _nextExprId
  }

  // Currently, this method is only used to prepare arguments to reflective calls.
  // This means it is safe to return AnyRef (as opposed to primitive types), because
  // reflection needs this anyway.
  private[codegen] def valueToJVM(e: Expr): AnyRef = e match {
    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(valueToJVM).toArray).asInstanceOf[AnyRef]

    case CaseClass(ccd, args) =>
      val cons = caseClassConstructors(ccd)
      cons.newInstance(args.map(valueToJVM).toArray : _*).asInstanceOf[AnyRef]

    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType) =>
      exprs.map(e => valueToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray

    // Just slightly overkill...
    case _ =>
      compileExpression(e, Seq()).evalToJVM(Seq())
  }

  // Note that this may produce untyped expressions! (typically: sets, maps)
  // re-implemented tail recursively
  private[codegen] def jvmToValue(e: AnyRef): Expr = {
    import scala.collection.immutable.Stack
    def postOrder(e : AnyRef) : Stack[AnyRef] = {
      @scala.annotation.tailrec
      def postOrderAcc(toSee: Stack[AnyRef], acc : Stack[AnyRef]) : Stack[AnyRef]= { 
        if (toSee.isEmpty) acc
        else {
          val (top, rest) = toSee.pop2
          top match {
            case _:Integer| _: java.lang.Boolean =>
              postOrderAcc(rest, acc push top)
            case cc: runtime.CaseClass =>
              val fields = cc.productElements()
              postOrderAcc(rest pushAll fields, acc push top)
            case tpl : runtime.Tuple =>
              val elems = for (i <- 0 until tpl.getArity) yield { tpl.get(i) }
              postOrderAcc(rest pushAll elems, acc push top)
            case set : runtime.Set => 
              val elems = set.getElements().asScala
              postOrderAcc(rest pushAll elems, acc push top)
            case map : runtime.Map =>
              val flatPairs = map.getElements().asScala.flatMap { entry =>
                Seq(entry.getKey(), entry.getValue())
              }
              postOrderAcc(rest pushAll flatPairs, acc push top)
            case _ =>
              throw CompilationException("Unsupported return value : " + top.getClass)
          }
        }

      }

      postOrderAcc(new Stack[AnyRef]().push(e), new Stack[AnyRef]())
    }

    def postOrderReconstruct(inp: Stack[AnyRef]) : Expr = {
      @scala.annotation.tailrec
      def postOrderAcc(inp : Stack[AnyRef], outp : Stack[Expr]) : Expr = {
        if (inp.isEmpty) outp.head
        else {
          val (top, rest) = inp.pop2
          top match {
            case i:Integer =>
              postOrderAcc(rest, outp push IntLiteral(i.toInt)) 
            case b: java.lang.Boolean =>
              postOrderAcc(rest, outp push BooleanLiteral(b.booleanValue)) 
            case cc: runtime.CaseClass =>
              jvmClassToDef.get(top.getClass.getName) match {
                case Some(ccd:CaseClassDef) =>
                  val (children, outp1) = outp.splitAt(cc.productElements().size)
                  val fields = children.toSeq.reverse
                  // We need to type any untypedfields
                  (fields zip ccd.fields) foreach { case (realF, formalF) => 
                    if (!realF.isTyped) realF.setType(formalF.getType)
                  }
                  val outCC = CaseClass(ccd, fields)
                  postOrderAcc(rest, outp1 push outCC)
                // FIXME added this
                case Some(_) => throw CompilationException("Unsupported return value : " + top)
                case None    => throw CompilationException("Unsupported return value : " + top)
              }
            case tpl : runtime.Tuple =>
              val (children, outp1) = outp.splitAt(tpl.getArity)
              val fields = children.toSeq.reverse
              // We need to type any untyped fields
              val outTpl = Tuple(fields)
              postOrderAcc(rest, outp1 push outTpl)
            case set : runtime.Set => 
              val (children, outp1) = outp.splitAt(set.size()) 
              val outSet = FiniteSet(children.toSeq.reverse)  // FIXME : If it is empty there is no way to reconstruct the type...
              postOrderAcc(rest, outp1 push outSet)
            case map : runtime.Map =>
              val (children, outp1) = outp.splitAt(2 * map.size()) 
              val (keys, vals) = children.zipWithIndex.partition {case (_, ind) => ind % 2 == 0}
              val outPairs = keys.zip(vals).map { case ( (key, _), (vl, _) ) => (key,vl) } 
              val outMap = FiniteMap(outPairs.toSeq.reverse)
              postOrderAcc(rest, outp1 push outMap)
          }
        }
      }

      postOrderAcc(inp, new Stack[Expr]())
        

    }

    postOrderReconstruct(postOrder(e))

    /*
    e match {
      case i: Integer =>
        IntLiteral(i.toInt)

      case b: java.lang.Boolean =>
        BooleanLiteral(b.booleanValue)

      case cc: runtime.CaseClass =>
        val fields = cc.productElements()

        jvmClassToDef.get(e.getClass.getName) match {
          case Some(cc: CaseClassDef) =>
            CaseClass(cc, fields.map(jvmToValue))
          case _ =>
            throw CompilationException("Unsupported return value : " + e)
        }

      case tpl: runtime.Tuple =>
        val elems = for (i <- 0 until tpl.getArity) yield {
          jvmToValue(tpl.get(i))
        }
        Tuple(elems)

      case set : runtime.Set =>
        FiniteSet(set.getElements().asScala.map(jvmToValue).toSeq)

      case map : runtime.Map =>
        val pairs = map.getElements().asScala.map { entry =>
          val k = jvmToValue(entry.getKey())
          val v = jvmToValue(entry.getValue())
          (k, v)
        }
        FiniteMap(pairs.toSeq)

      case _ =>
        throw CompilationException("Unsupported return value : " + e.getClass)
    }*/
  }

  def compileExpression(e: Expr, args: Seq[Identifier]): CompiledExpression = {
    if(e.getType == Untyped) {
      throw new IllegalArgumentException("Cannot compile untyped expression [%s].".format(e))
    }

    val id = nextExprId

    val cName = "Leon$CodeGen$Expr$"+id

    val cf = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    val argsTypes = args.map(a => typeToJVM(a.getType))

    val realArgs = if (env.params.requireMonitor) {
      ("L" + CodeGeneration.MonitorClass + ";") +: argsTypes
    } else {
      argsTypes
    }

    val m = cf.addMethod(
      typeToJVM(e.getType),
      "eval",
      realArgs : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val newMapping    = if (env.params.requireMonitor) {
        args.zipWithIndex.toMap.mapValues(_ + 1)
      } else {
        args.zipWithIndex.toMap
      }

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(e)

    mkExpr(e, ch)(env.withVars(newMapping))

    e.getType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case UnitType | _: TupleType  | _: SetType | _: MapType | _: AbstractClassType | _: CaseClassType | _: ArrayType =>
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze

    loader.register(cf)

    new CompiledExpression(this, cf, e, args)
  }

  // writeClassFiles
}

object CompilationUnit {
  def compileProgram(p: Program, params: CodeGenParams = CodeGenParams()): Option[CompilationUnit] = {
    implicit val env = CompilationEnvironment.fromProgram(p, params)

    var classes = Map[Definition, ClassFile]()

    for((parent,children) <- p.algebraicDataTypes) {
      classes += parent -> compileAbstractClassDef(parent)

      for (c <- children) {
        classes += c -> compileCaseClassDef(c)
      }
    }

    for(single <- p.singleCaseClasses) {
      classes += single -> compileCaseClassDef(single)
    }

    val mainClassName = defToJVMName(p.mainObject)
    val cf = new ClassFile(mainClassName, None)

    classes += p.mainObject -> cf

    cf.addDefaultConstructor

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    // This assumes that all functions of a given program get compiled
    // as methods of a single class file.
    for(funDef <- p.definedFunctions;
        (_,mn,_) <- env.funDefToMethod(funDef)) {

      val argsTypes = funDef.args.map(a => typeToJVM(a.tpe))
      val realArgs = if (env.params.requireMonitor) {
        ("L" + CodeGeneration.MonitorClass + ";") +: argsTypes
      } else {
        argsTypes
      }

      val m = cf.addMethod(
        typeToJVM(funDef.returnType),
        mn,
        realArgs : _*
      )
      m.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL |
        METHOD_ACC_STATIC
      ).asInstanceOf[U2])

      compileFunDef(funDef, m.codeHandler)
    }

    Some(new CompilationUnit(p, classes, env))
  }
}
