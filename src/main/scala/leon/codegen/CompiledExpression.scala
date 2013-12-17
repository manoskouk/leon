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

import runtime.LeonCodeGenRuntimeMonitor

import java.lang.reflect.InvocationTargetException

class CompiledExpression(unit: CompilationUnit, cf: ClassFile, expression : Expr, argsDecl: Seq[Identifier]) {
  private lazy val cl = unit.loader.loadClass(cf.className)
  private lazy val meth = cl.getMethods()(0)

  private val exprType = expression.getType

  private val params = unit.env.params

  def argsToJVM(args: Seq[Expr]): Seq[AnyRef] = {
    args.map(unit.valueToJVM)
  }

  def evalToJVM(args: Seq[AnyRef]): AnyRef = {
    assert(args.size == argsDecl.size)

    val realArgs = if (params.requireMonitor) {
      new LeonCodeGenRuntimeMonitor(params.maxFunctionInvocations) +: args
    } else {
      args
    }

    if (realArgs.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, realArgs.toArray : _*)
    }
  }

  // This may throw an exception. We unwrap it if needed.
  // We also need to reattach a type in some cases (sets, maps).
  def evalFromJVM(args: Seq[AnyRef]) : Expr = {
    try {
      val result = unit.jvmToValue(evalToJVM(args))
      if(!result.isTyped) {
        result.setType(exprType)
      }
      result
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }

  def eval(args: Seq[Expr]) : Expr = {
    try {
      evalFromJVM(argsToJVM(args))
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }

  // Apply function recursively howMany times, which is of type (A, Int) => A
  // Memoization-specific
  // FIXME: Could write straight bytecode for this
  def recEval(arg: Expr, howMany : Int) : Expr = {
    try {
      // pseudorandom input
      def psr(i : Int) = (347837 * i + 983876) % 98291
/*
      val jvmArg = unit.valueToJVM(arg)
      // Not optimized?
      def rec(jvmArg: AnyRef, howMany: Int) : AnyRef = {
        if (howMany == 0) jvmArg
        else { 
          val jvmInp = unit.valueToJVM( IntLiteral(psr(howMany)) )
          rec( evalToJVM(Seq(jvmArg, jvmInp)), howMany-1 )
        }
      }
      
      unit.jvmToValue(rec(jvmArg, howMany))*/
      
      var jvmArg = unit.valueToJVM(arg)
      var i = howMany
      while(i > 0) { 
        val jvmInp = unit.valueToJVM(IntLiteral(psr(i)))
        jvmArg = evalToJVM(Seq(jvmArg,jvmInp))
        i = i - 1
      }

      unit.jvmToValue(jvmArg)

    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }


} 
