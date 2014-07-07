/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.memoization

import leon._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import memoization._

import verification.AnalysisPhase

import utils.{DebugSectionMemoization}

import evaluators.{CodeGenEvaluator, EvaluationResults}
import evaluators.EvaluationResults._
import codegen.{CodeGenParams,CompilationUnit}

import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}

//import org.scalameter.{PerformanceTest,persistence,Executor,Gen}
import org.scalameter.api._//exec

object MemoFootprint extends PerformanceTest.OfflineRegressionReport {

  // Time a block and return time in millisec.
  def time[A]( block : => A) : (A, Double) = {
    val before = System.nanoTime
    val res    = block
    val after  = System.nanoTime 
    (res, ((after - before) *10 /1000000).toDouble * 0.1)
  }

 

    
  private def testMemo(f : String, how : MemoTestOptions.HowToTest, index:Int) : Expr = { 
    import MemoTestOptions._

    def compileTestFun(p : Program ,ctx : LeonContext) : (Expr, (Expr, Int) => EvaluationResults.Result) = {
      // We want to produce code that checks contracts
      val evaluator = new CodeGenEvaluator(ctx, p , CodeGenParams(checkContracts = true))
      how match { 
        case MemoTestOptions.Incremental => {
          // Incremental have two functions: 
          // init() : structure, which gives the initial value (Nil etc)
          // test(structure,element) : structure, which is the incremental test operation (insert etc)
          val testFun =  p.definedFunctions.find(_.id.name == "test").getOrElse {
            ctx.reporter.fatalError("Test function not defined!")
          }
          val initVal = p.definedFunctions.find(_.id.name == "init").getOrElse {
            ctx.reporter.fatalError("Initial value not defined!")
          }.body.get

          val params = testFun.params map { _.id }
          val body = testFun.body.get

          // Will apply test a number of times with the help of compileRec
          (
            initVal, evaluator.compileRec(body, params).getOrElse{
              ctx.reporter.fatalError("Failed to compile test function!")
            }
          )
        }

        case MemoTestOptions.Bulk => {
          // Bulk benchmarks have 3 functions: 
          // init() : structure , which gives the initial value (Nil etc)
          // simpleInsert(structure, element) : structure , which is the trivial insertion (e.g. cons)
          // test(structure), which is the bulk operation we will test (e.g. sort)


          val evaluator = new CodeGenEvaluator(ctx, p , CodeGenParams(checkContracts = true))
          val testFun =  p.definedFunctions.find(_.id.name == "test").getOrElse {
            ctx.reporter.fatalError("Test function not defined!")
          }
          val initVal = p.definedFunctions.find(_.id.name == "init").getOrElse {
            ctx.reporter.fatalError("Initial value not defined!")
          }.body.get
          val simpleInsert = p.definedFunctions.find(_.id.name == "simpleInsert").getOrElse {
            ctx.reporter.fatalError("simpleInsert function not defined!")
          }


          val args = simpleInsert.params map { _.id }
          val body = simpleInsert.body.get

          val construct = evaluator.compileRec(body, args).getOrElse{
            ctx.reporter.fatalError("Failed to compile simpleInsert function!")
          }
          val test = evaluator.compile(testFun.body.get, testFun.params.map{_.id}).getOrElse{
            ctx.reporter.fatalError("Failed to compile test function!")
          }

          // The complete function will construct a structure with compileRec, then apply 
          // the test operation with compile
          def complete(init: Expr, howMany : Int) : EvaluationResults.Result = 
            construct(init,howMany) match {
              case Successful(ex) => test(Seq(ex))
              case err : RuntimeError => err
              case err : EvaluatorError => err
            }

          (initVal, complete)
        }
      }
    }
    
    val pipeFront = 
      utils.TemporaryInputPhase andThen
      frontends.scalac.ExtractionPhase andThen
      utils.ScopingPhase andThen
      purescala.MethodLifting andThen
      utils.SubtypingPhase andThen
      purescala.CompleteAbstractDefinitions 

  
    // Compile original file
    val timeOut = 2
    
  
    val settings = Settings(
      memo = true, 
      debugSections = Set(DebugSectionMemoization), 
      injectLibrary = false,
      strictCompilation = false
    )
    val reporter = new leon.DefaultReporter(settings)
    val ctx = LeonContext(
      files = List(),
      reporter = reporter,
      interruptManager = new leon.utils.InterruptManager(reporter),
      settings = settings,
      options =  Seq(LeonFlagOption("library", false), LeonValueOption("timeout", timeOut.toString))
    )

    val whatToRun = index match {
      case 0 =>
        val orig = pipeFront.run(ctx)(f, List())
        orig
      case 1 =>
        val origNC = {
          val orig = purescala.ScalaPrinter((
            pipeFront andThen 
            AnalysisPhase andThen 
            ExcludeVerifiedPhase
          ). run(ctx) ((f,List())))
          pipeFront.run(ctx)(orig,List())
        }
        origNC
      case 2 => 
        val trans = {
          val orig = purescala.ScalaPrinter(
              (pipeFront andThen      
              MemoizationPhase). run(ctx) ((f,List())))
          pipeFront.run(ctx)(orig,List())
        }
        trans
      case 3 => 
        val transNC = {
          val orig = purescala.ScalaPrinter(
              (pipeFront andThen 
              AnalysisPhase andThen 
              ExcludeVerifiedPhase andThen
              MemoizationPhase). run(ctx) ((f,List())))
          pipeFront.run(ctx)(orig,List())
        }
        transNC
    }
  
/*
    ctx.reporter.info("Compiling original to bytecode")
    val (init1, compiled1) = compileTestFun(orig,ctx)
    ctx.reporter.info("Compiling original, FCs removed to bytecode")
    val (init2, compiled2) = compileTestFun(origNC,ctx)
    ctx.reporter.info("Compiling transformed to bytecode")
    val (init3, compiled3) = compileTestFun(trans,ctx)
    ctx.reporter.info("Compiling transformed, FCs removed to bytecode")
    val (init4, compiled4) = compileTestFun(transNC,ctx)
*/
    
    val (init, compiled) = compileTestFun(whatToRun, ctx)
    val size = 250
    /*
    val whatToRun = List(
      (testOriginal,  compiled1, init1, "        Original"),
      (testOriginalR, compiled2, init2, "    OriginalRem."),
      (testTrans,     compiled3, init3, "     Transformed"),
      (testTransR,    compiled4, init4, " TransformedRem.")
    )(index)
        
    whatToRun._2(whatToRun._3, size).result.get
    */

    compiled(init, size).result.get
  }
  
  override def persistor = new org.scalameter.persistence.SerializationPersistor
    
  override def measurer = new Measurer.MemoryFootprint

  def  heapSort() = """
    //import leon.lang._

    object HeapSort {
      sealed abstract class List
      case class Cons(head:Int,tail:List) extends List
      case class Nil() extends List
    
      sealed abstract class Heap
      case class Leaf() extends Heap
      case class Node(value: Int, left: Heap, right: Heap) extends Heap
    
      //O(logn) assuming leftist
      private def rank(h: Heap) : Int = h match {
        case Leaf() => 0
        case Node(_,_,r) => rank(r) + 1
      }
    
      // O(nlogn) -- will be called on each node once
      private def hasLeftistProperty(h: Heap) : Boolean = h match {
        case Leaf() => true
        case Node(_,l,r) => hasLeftistProperty(l) && hasLeftistProperty(r) && rank(l) >= rank(r)
      }
    
      // O(n^2logn)
      def heapSize(t: Heap): Int = {
        require(hasLeftistProperty(t))
        (t match {
          case Leaf() => 0
          case Node(v, l, r) => heapSize(l) + 1 + heapSize(r)
        })
      } ensuring(_ >= 0)
    
      // O(n^2logn) + T(n/2)
      // O(n^2logn)
      private def merge(h1: Heap, h2: Heap) : Heap = {
        require(hasLeftistProperty(h1) && hasLeftistProperty(h2))
        h1 match {
          case Leaf() => h2
          case Node( v1, l1, r1) => h2 match {
            case Leaf() => h1
            case Node( v2, l2, r2) =>
              if(v1 > v2)
                makeT(v1, l1, merge(r1, h2))
              else
                makeT(v2, l2, merge(h1, r2))
          }
        }
      } ensuring(res => hasLeftistProperty(res) && heapSize(h1) + heapSize(h2) == heapSize(res))
    
      // O(logn)
      private def makeT(value: Int, left: Heap, right: Heap) : Heap = {
        if(rank(left) >= rank(right))
          Node(value, left, right)
        else
          Node(value, right, left)
      }
    
      // O(n^2logn)
      def insert(element: Int, heap: Heap) : Heap = {
        require(hasLeftistProperty(heap))
    
        merge(Node(element, Leaf(), Leaf()), heap)
    
      } ensuring(res => heapSize(res) == heapSize(heap) + 1)
    
      // O(nlogn)
      def findMax(h: Heap) : Int = {
        require(hasLeftistProperty(h))
        h match {
          case Node(m,_,_) => m
          case Leaf() => -1000
        }
      }
    
      // O(n^2logn)
      def removeMax(h: Heap) : Heap = {
        require(hasLeftistProperty(h))
        h match {
          case Node(_,l,r) => merge(l, r)
          case l @ Leaf() => l
        }
      }
    
      def listSize(l : List) : Int = (l match {
        case Nil() => 0
        case Cons(_, xs) => 1 + listSize(xs)
      }) ensuring(_ >= 0)
    
      // O(n^3logn)
      def removeElements(h : Heap, l : List) : List = {
       require(hasLeftistProperty(h))
       h match {
        case Leaf() => l
        case _ => removeElements(removeMax(h),Cons(findMax(h),l))
    
      }} ensuring(res => heapSize(h) + listSize(l) == listSize(res))
    
      // O(n^2logn) for each node
      // O(n^3logn)
      def buildHeap(l : List, h: Heap) : Heap = {
       require(hasLeftistProperty(h))
       l match {
        case Nil() => h
        case Cons(x,xs) => buildHeap(xs, insert(x, h))
    
      }} ensuring(res => hasLeftistProperty(res) && heapSize(h) + listSize(l) == heapSize(res))
    
      // O(n^3logn)
      def sort(l: List): List = ({
    
        val heap = buildHeap(l,Leaf())
        removeElements(heap, Nil())
    
      }) ensuring(res => listSize(res) == listSize(l))
    
      /*
      // pseudorandom els. to insert
      def psr (input : Int) : Int = {
        (input * 476272 + 938709) % 187987
      }
      def rec(size : Int, acc : List) : List = {
        if (size == 0) acc
        else rec(size -1, Cons(psr(size),acc))
      }
      
      def test(size : Int) : List = { 
          val l = rec(size, Nil())
          sort(l)
      }
    */
      
      def init() : List = Nil()
      def simpleInsert(l : List, i : Int) = Cons(i,l)
      def test(l : List) : List = sort(l)
    
    }
  """
  
  def rbTree() = """
    import scala.collection.immutable.Set
    //import leon.annotation._
    //import leon.lang._
    
    object RedBlackTree { 
      sealed abstract class Color
      case class Red() extends Color
      case class Black() extends Color
     
      sealed abstract class Tree
      case class Empty() extends Tree
      case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree
    
      sealed abstract class OptionInt
      case class Some(v : Int) extends OptionInt
      case class None() extends OptionInt
    
      def content(t: Tree) : Set[Int] = t match {
        case Empty() => Set.empty
        case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
      }
    
      def size(t: Tree) : Int = t match {
        case Empty() => 0
        case Node(_, l, v, r) => size(l) + 1 + size(r)
      }
    
      /* We consider leaves to be black by definition */
      def isBlack(t: Tree) : Boolean = t match {
        case Empty() => true
        case Node(Black(),_,_,_) => true
        case _ => false
      }
    
      def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
        case Empty() => true
        case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
        case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
      }
    
      def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
        case Empty() => true
        case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
      }
    
      def blackBalanced(t : Tree) : Boolean = t match {
        case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
        case Empty() => true
      }
    
      def blackHeight(t : Tree) : Int = t match {
        case Empty() => 1
        case Node(Black(), l, _, _) => blackHeight(l) + 1
        case Node(Red(), l, _, _) => blackHeight(l)
      }
    
    
      def orderedKeys(t : Tree) : Boolean = orderedKeys(t, None(), None())
    
      def orderedKeys(t : Tree, min : OptionInt, max : OptionInt) : Boolean = t match {
        case Empty() => true
        case Node(c,a,v,b) =>
          val minOK = 
            min match {
              case Some(minVal) =>
                v > minVal
              case None() => true
            }
          val maxOK =
            max match {
              case Some(maxVal) =>
                v < maxVal
              case None() => true
            }
          minOK && maxOK && orderedKeys(a, min, Some(v)) && orderedKeys(b, Some(v), max)
      }
    
      // <<insert element x into the tree t>>
      def ins(x: Int, t: Tree): Tree = {
        require(redNodesHaveBlackChildren(t) && blackBalanced(t) && orderedKeys(t))
        t match {
          case Empty() => Node(Red(),Empty(),x,Empty())
          case Node(c,a,y,b) =>
            if      (x < y)  balance(Node(c, ins(x, a), y, b))
            else if (x == y) Node(c,a,y,b)
            else             balance(Node(c,a,y,ins(x, b)))
        }
      } ensuring (res => 
        content(res) == content(t) ++ Set(x) && 
        size(t) <= size(res) && size(res) <= size(t) + 1  && 
        redDescHaveBlackChildren(res)  && 
        blackBalanced(res) && 
        orderedKeys(res)
      )
    
      def makeBlack(n: Tree): Tree = {
        require(redDescHaveBlackChildren(n) && blackBalanced(n) && orderedKeys(n))
        n match {
          case Node(Red(),l,v,r) => Node(Black(),l,v,r)
          case _ => n
        }
      } ensuring(res => 
        redNodesHaveBlackChildren(res) && 
        blackBalanced(res) && 
        orderedKeys(res) && 
        content(res) == content(n) 
      )
    
      def add(x: Int, t: Tree): Tree = {
        require(redNodesHaveBlackChildren(t) && blackBalanced(t) && orderedKeys(t))
        makeBlack(ins(x, t))
      } ensuring (res => 
        content(res) == content(t) ++ Set(x) && 
        redNodesHaveBlackChildren(res) && 
        blackBalanced(res) && 
        orderedKeys(res)
      )
      
      def balance(t : Tree) : Tree = { //c: Color, a: Tree, x: Int, b: Tree): Tree = {
        require(orderedKeys(t))
        //require(orderedKeys(a, None(), Some(x)) && orderedKeys(b, Some(x), None()))
        // require(
        //   Node(c,a,x,b) match {
        //     case Node(Black(),Node(Red(),Node(Red(),a,_,b),_,c),_,d) =>
        //       redNodesHaveBlackChildren(a) &&
        //       redNodesHaveBlackChildren(b) &&
        //       redNodesHaveBlackChildren(c) &&
        //       redNodesHaveBlackChildren(d)
        //     case Node(Black(),Node(Red(),a,_,Node(Red(),b,_,c)),_,d) =>
        //       redNodesHaveBlackChildren(a) &&
        //       redNodesHaveBlackChildren(b) &&
        //       redNodesHaveBlackChildren(c) &&
        //       redNodesHaveBlackChildren(d)
        //     case Node(Black(),a,_,Node(Red(),Node(Red(),b,_,c),_,d)) => 
        //       redNodesHaveBlackChildren(a) &&
        //       redNodesHaveBlackChildren(b) &&
        //       redNodesHaveBlackChildren(c) &&
        //       redNodesHaveBlackChildren(d)
        //     case Node(Black(),a,_,Node(Red(),b,_,Node(Red(),c,_,d))) => 
        //       redNodesHaveBlackChildren(a) &&
        //       redNodesHaveBlackChildren(b) &&
        //       redNodesHaveBlackChildren(c) &&
        //       redNodesHaveBlackChildren(d)
        //     case t => redDescHaveBlackChildren(t)
        //   }
        // )
        t match {
          case Empty() => Empty() 
          case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
            Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
          case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
            Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
          case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
            Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
          case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
            Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
          case Node(c,a,xV,b) => Node(c,a,xV,b)
        }
      } ensuring (res => 
        content(res) == content(t) && 
        orderedKeys(res)
      )// && redDescHaveBlackChildren(res))
    
      // def buggyBalance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
      //   Node(c,a,x,b) match {
      //     case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
      //       Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      //     case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
      //       Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      //     case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
      //       Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      //     case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
      //       Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      //   }
      // } ensuring (res => content(res) == content(Node(c,a,x,b)) ) // && redDescHaveBlackChildren(res))
    
      //@verified
      //def generateRB(t : Tree) : Boolean = (blackHeight(t) != 3 || !blackBalanced(t) || !orderedKeys(t)) holds
      //@verified
      def test(t : Tree, i : Int) = add(i,t)
      def init() = Empty()
    }
"""
def avl() = """
import leon.lang._
import leon.annotation._
object AVLTree  {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(left : Tree, value : Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class None() extends OptionInt
  case class Some(i:Int) extends OptionInt


  def smallerOption(o1:OptionInt,o2:OptionInt) : Boolean  = {
    (o1,o2) match {
      case (Some(i1), Some(i2)) => i1 < i2
      case (_,_) => true
    }
  }

  def minOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1<=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )
  
  def maxOption(o1:OptionInt,o2:OptionInt) : OptionInt = (
    (o1,o2) match {
      case (Some(i1), Some(i2)) => Some(if (i1>=i2) i1 else i2)
      case (Some(_), _) => o1
      case (_, Some(_)) => o2
      case _ => None()
    }
  )

  def min(i1:Int, i2:Int) : Int = if (i1<=i2) i1 else i2
  def max(i1:Int, i2:Int) : Int = if (i1>=i2) i1 else i2

  private def size(t: Tree): Int = {
    (t match {
      case Leaf() => 0
      case Node(l, _, r) => size(l) + 1 + size(r)
    })
  } ensuring (_ >= 0)
 
  // O(n)
  @forceMemo
  def height(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  } ensuring(_ >= 0)

  def treeMax(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => maxOption(Some(v), maxOption (treeMax(l), treeMax(r)))
    }
  }

  def treeMin(t:Tree) : OptionInt = {
    t match {
      case Leaf()      => None()
      case Node(l,v,r) => minOption(Some(v), minOption (treeMin(l), treeMin(r)))
    }
  }

  // O(nlogn) assuming balanced
  def content(t : Tree) : Set[Int] = t match {
    case Leaf() => Set.empty[Int]
    case Node(l,v,r) => content(l) ++ Set[Int](v) ++ content(r)
  }

  def isBST(t:Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        if (isBST(l) && isBST(r)) {
          smallerOption(Some(v),bstMin(r)) && 
          smallerOption(bstMax(l),Some(v))
        }
        else false 
    }
  }

  // O(n)
  def balanceFactor(t : Tree) : Int = {
    t match{
      case Leaf() => 0
      case Node(l, _, r) => height(l) - height(r)
    }
  } 
  
  // O(nlogn) assuming balanced trees
  def isAVL(t:Tree) : Boolean = {    
    t match {
        case Leaf() => true        
        case Node(l,v,r) =>  
          isAVL(l) && isAVL(r) && 
          smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) &&
          balanceFactor(t) >= -1 && balanceFactor(t) <= 1 
      }    
  } 

  def bstMax(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None() 
      case Node(_,v,Leaf()) => Some(v) 
      case Node(_,_,r)      => bstMax(r)
    }
  } ensuring (res => res == treeMax(t))

  def bstMin(t:Tree) : OptionInt = {
    require(isBST(t))
    t match {
      case Leaf() => None()
      case Node(Leaf(),v,_) => Some(v) 
      case Node(l,     _,_) => bstMin(l)
    }
  } ensuring (res => res == treeMin(t))
  
  // O(nlogn)
  def offByOne(t : Tree) : Boolean = {
    t match {
      case Leaf() => true
      case Node(l,v,r) => 
        isAVL(l) && isAVL(r) && 
        balanceFactor(t) >= -2 && balanceFactor(t) <= 2 &&
        smallerOption(treeMax(l),Some(v)) && smallerOption(Some(v),treeMin(r)) 
    }
  }

  // T1(n) = O(nlogn) + T2(n/2)  
  // O(nlogn)
  @induct
  def unbalancedInsert(t: Tree, e : Int) : Tree = {
    require(isAVL(t))
    t match {
      case Leaf() => Node(Leaf(), e, Leaf())
      case Node(l,v,r) => 
             if (e == v) t
        else if (e <  v){
          val newl = avlInsert(l,e)
          Node(newl, v, r)
        } 
        else {
          val newr = avlInsert(r,e)
          Node(l, v, newr)
        }            
    }
  } ensuring(res => offByOne(res) && content(res) == content(t) ++ Set[Int](e))
             
  // T2(n) = O(nlogn) + T1(n) 
  // O(nlogn)
  def avlInsert(t: Tree, e : Int) : Tree = {    
    require(isAVL(t))
    
    balance(unbalancedInsert(t,e))
    
  } ensuring(res => 
    isAVL(res) && 
    height(res) >= height(t) && 
    height(res) <= height(t) + 1 && 
    size(res) <= size(t) + 1 &&
    content(res) == content(t) ++ Set[Int](e)
  )
     
  // O(nlogn)
  def balance(t:Tree) : Tree = {
    require(offByOne(t)) //isBST(t) && 
    t match {
      case Leaf() => Leaf() // impossible...
      case Node(l, v, r) => 
        val bfactor = balanceFactor(t)
        // at this point, the tree is unbalanced
        if(bfactor > 1 ) { // left-heavy
          val newL = 
            if (balanceFactor(l) < 0) { // l is right heavy
              rotateLeft(l)
            }
            else l
          rotateRight(Node(newL,v,r))
        }
        else if(bfactor < -1) { //right-heavy
          val newR = 
            if (balanceFactor(r) > 0) { // r is left heavy
              rotateRight(r)
            }
            else r
          rotateLeft(Node(l,v,newR))
        } else t        
      } 
    } ensuring(res => isAVL(res) && content(res) == content(t))

  def rotateRight(t:Tree) = {    
    t match {
      case Node(Node(ll, vl, rl),v,r) =>
        
        val hr = max(height(rl),height(r)) + 1        
        Node(ll, vl, Node(rl,v,r))
        
      case _ => t // this should not happen
  } }
   
 
  def rotateLeft(t:Tree) =  {    
    t match {
      case Node(l, v, Node(lr,vr,rr)) => 
                
        val hl = max(height(l),height(lr)) + 1        
        Node(Node(l,v,lr), vr, rr)
      case _ => t // this should not happen
  } } 

 /* 
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : Tree) : Tree = {
    if (size == 0) acc
    else rec(size -1, avlInsert(acc, psr(size)))
  }

 
  def test(size : Int) : Tree = { 
    
    rec(size, Leaf())

  }
*/

  def test(t:Tree, i:Int) = { 
    //require(isAVL(t))
    avlInsert(t,i)
  }
  def init() = Leaf()

}
"""
  
  def amq() = """
import leon.annotation._
import leon.lang._

object AmortizedQueue {

  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def q2l(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def nth(l:List, n:Int) : Int = {
    require(0 <= n && n < size(l))
    l match {
      case Cons(x,xs) =>
    if (n==0) x else nth(xs, n-1)
    }
  }

  def l2mFrom(k:Int, l:List) : Map[Int,Int] = (l match {
    case Nil() => Map[Int,Int]()
    case Cons(x,xs) => l2mFrom(k+1,xs).updated(k,x)
  })

  def l2m(l:List) : Map[Int,Int] = l2mFrom(0,l)

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2)  && content(res) == content(l1) ++ content(l2))

  def concatTest(l1 : List, l2 : List, i:Int) : List = ({
    require(0 <= i && i < size(l1) + size(l2))
    l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x,
                  if (i == 0) concat(xs, l2)
                  else concatTest(xs, l2, i-1))
    }
  }) ensuring (res => size(res) == size(l1) + size(l2) &&
           content(res) == content(l1) ++ content(l2) &&
           nth(res,i) == (if (i < size(l1)) nth(l1,i) else nth(l2,i-size(l1))) &&
           res == concat(l1,l2))

  def nthConcat(l1:List, l2:List, i:Int) : Boolean = {
    require(0 <= i && i < size(l1) + size(l2))
    concatTest(l1, l2, i) == concatTest(l1, l2, i) &&
    nth(concat(l1,l2), i) == (if (i < size(l1)) nth(l1,i) else nth(l2,i-size(l1)))
  } holds

  def sameUpto(l1:List, l2:List, k:Int) : Boolean = {
    require(0 <= k)
    (l1,l2) match {
      case (Nil(),Nil()) => true
      case (Nil(),_) => false
      case (_,Nil()) => false
      case (Cons(x,xs),Cons(y,ys)) => {
    x==y && (if (k==0) true else sameUpto(xs,ys,k-1))
      }
    }
  } ensuring(res => !(size(l1)==k && size(l2)==k && res) || l1==l2)

  @induct
  def concatAssoc(l1:List, l2:List, l3:List) : Boolean = {
    concat(l1, concat(l2,l3)) == concat(concat(l1,l2), l3)
  } holds

  def concatCons(x:Int, l2:List, l3:List) : Boolean = {
    Cons(x, concat(l2,l3)) == concat(Cons(x,l2), l3)
  } holds

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def rev1(l : List, acc: List) : List = { l match {
    case Nil() => acc
    case Cons(x,xs) => rev1(xs, Cons(x,acc))
  }} ensuring { res => size(res) == size(l) + size(acc) && content(res) == content(l) ++ content(acc) }

  def reverse(l : List) : List = { rev1(l, Nil()) 
  } ensuring (res => content(res) == content(l) && size(res) == size(l))

  def revConcatNth(l1:List, l2:List, i:Int) : Boolean = {
    require(0 <= i && i < size(l1)+size(l2))
    nth(reverse(concat(l1,l2)),i) == nth(concat(reverse(l2), reverse(l1)),i)
  } holds

  def revrev(l:List) : Boolean = {
    reverse(reverse(l)) == l
  } holds

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } ensuring(res => isAmortized(res) && q2l(Queue(front, rear)) == q2l(res))

  def isEmpty(queue : AbsQueue) : Boolean = (queue match {
      case Queue(Nil(), Nil()) => true
      case _ => false
  }) ensuring(res => (res == (q2l(queue) == Nil())))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(res => isAmortized(res) && q2l(res) == concat(q2l(queue), Cons(elem, Nil())))
    // this did not find a counterexample:
    // ensuring(res => isAmortized(res) && q2l(res) == Cons(elem, q2l(queue)))

  def push(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(Cons(elem,front), rear)
  }) ensuring(res => isAmortized(res) && q2l(res) == Cons(elem, q2l(queue)))


 // I did not know why this does not type check
  def matchQ(queue : AbsQueue) : (Int, AbsQueue) = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => (f, amortizedQueue(fs, rear))
    }
  }) ensuring(res => {
    val (f,q) = res
    q2l(queue) == Cons(f, q2l(q))
  })

  def tail(queue : AbsQueue) : AbsQueue = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  }) ensuring(res => isAmortized(res) && (q2l(queue) match {
    case Nil() => false
    case Cons(_,xs) => q2l(res)==xs
  }))

  def front(queue : AbsQueue) : Int = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }) ensuring(res => q2l(queue) match {
    case Nil() => false
    case Cons(x,_) => x==res
  })

  // @induct
  // def propEnqueue(rear : List, front : List, list : List, elem : Int) : Boolean = {
  //   require(isAmortized(Queue(front, rear)))
  //   val queue = Queue(front, rear)
  //   if (q2l(queue) == list) {
  //     q2l(enqueue(queue, elem)) == concat(list, Cons(elem, Nil()))
  //   } else
  //     true
  // } holds

  @induct
  def propFront(queue : AbsQueue, list : List, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (q2l(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  } holds

  @induct
  def propTail(rear : List, front : List, list : List, elem : Int) : Boolean = {
    require(!isEmpty(Queue(front, rear)) && isAmortized(Queue(front, rear)))
    if (q2l(Queue(front, rear)) == list) {
      list match {
        case Cons(_, xs) => q2l(tail(Queue(front, rear))) == xs
      }
    } else
      true
  } // holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  } holds

  def enqueueDequeueThrice(queue : AbsQueue, e1 : Int, e2 : Int, e3 : Int) : Boolean = {
    if (isEmpty(queue)) {
      val q1 = enqueue(queue, e1)
      val q2 = enqueue(q1, e2)
      val q3 = enqueue(q2, e3)
      val e1prime = front(q3)
      val q4 = tail(q3)
      val e2prime = front(q4)
      val q5 = tail(q4)
      val e3prime = front(q5)
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  } holds
  
  def emptyQueue() : AbsQueue = Queue(Nil(), Nil())

/*  // pseudorandom els. to insert
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : AbsQueue) : AbsQueue = {
    if (size == 0) acc
    else rec(size -1, enqueue(acc, psr(size)))
  }
  
  def test(size : Int) : AbsQueue = { 
      rec(size, emptyQueue)
  }
*/
  def test(q:AbsQueue, i:Int) : AbsQueue = enqueue(q,i)
  def init() : AbsQueue = emptyQueue()

}



"""

  //val sizes = Gen.range("size")(1000000, 5000000, 2000000)
  
  val test1 = Gen.range("index")(0,3,1) 

  performance of "MemoryFootprint" in {
    performance of "heap" in {
      using(test1) config (
        exec.benchRuns -> 10,
        exec.independentSamples -> 2,
        exec.jvmflags -> "-Xss1G"      
      ) in { ind =>
        //val hs = heapSort()
        //testMemo(hs, MemoTestOptions.Bulk, ind)
        val theTest = amq()
        testMemo(theTest, MemoTestOptions.Incremental, ind)
      }
    }
  }

  /*
  performance of "MemoryFootprint" in {
    performance of "testMemo" in {
      using(Gen.range("ind")(0,3,1)) config (
        exec.independentSamples -> 6
      ) in { ind =>
        testMemo(test._1, test._2, ind )
      }
    }
  }*/

  
 }
