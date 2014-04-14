/* Copyright 2009-2013 EPFL, Lausanne */

package leon.memoization

import leon._

import utils._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps.{variablesOf,functionCallsOf,preMap,applyOnFunDef,preMapOnFunDef,replaceFromIDs}
import purescala.TypeTrees._
import purescala.TypeTreeOps.{typeParamSubst,instantiateType}

import verification.{VerificationReport,VerificationCondition}


object MemoizationPhase extends TransformationPhase {

  val name = "Memoization transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep Memoization information"
  override val definedOptions : Set[LeonOptionDef] = Set( 
    LeonFlagOptionDef("no-verify", "--no-verify", "Skip verification before memoization transformation.")
  )

  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  

  // Identifier printing strategy. true is mostly for debugging
  private val alwaysShowUniqueId = false 
  private def freshIdentifier (name : String) = FreshIdentifier(name, alwaysShowUniqueId)

  def acceptableParams(f : FunDef) = {
      f.params.size == 1 ||
      f.params.size == 2 && f.params.tail.head.id.name == "__isVerified"
    }
  
  /**
   * A tree structure, homomorphic to the structure of a class tree in the program,
   * which stores extra information/methods to help the analysis
   */
  private trait MemoClassRecord{
    
    val p : Program
    val candidateFuns : Set[FunDef]
    val parent : Option[MemoAbstractClassRecord] 
  
    type A <: ClassDef
    val classDef : A
    def classType = classDefToClassType(classDef)

    // Return some fresh type parameters, based on those of classDef
    def freshenClassDefTpParams() = for (tp <- classDef.tparams) yield TypeParameter(tp.id.freshen)    
    
    // Functions which recursively call themselves with their only argument being of type classDef
    val classDefRecursiveFuns : Seq[FunDef] = candidateFuns.toSeq filter { f =>
      f.params.head.getType.asInstanceOf[ClassType].classDef == classDef 
    }
    val hasLocalMemoFuns = !classDefRecursiveFuns.isEmpty
    
    // The extra field that this type will get, with sub-fields memoizing classDefRecursveFuns
    val extraField : Option[CaseClassDef] = {
      if (!hasLocalMemoFuns) None 
      else Some ({
        val concr = new CaseClassDef(
          id = freshIdentifier(classDef.id + "Fields"),
          tparams= freshenClassDefTpParams() map TypeParameterDef, // FIXME Maybe we don't need them all
          parent = None, 
          false 
        )
        concr.setFields( for (fn <- classDefRecursiveFuns) yield {  
          new ValDef(fn.id.freshen, fn.returnType) 
        })
        concr
      })
    }


    val children : Seq[MemoClassRecord]
    lazy val descendents : Seq[MemoClassRecord] = collectFromTree { node => node }    
    lazy val caseDescendents = for (desc@MemoCaseClassRecord(_,_,_,_) <- descendents) yield desc
    
    // How many fields were added to the class
    protected var extraFieldsNo = 0

    // Add all memoized functions from top of the tree as fields
    // Works with side effects!
    def enrichClassDef() : Unit
    enrichClassDef()
    
    // A new constructor for the caseclass type to make sure 
    // all fields are created with invariants
    val constructor: Option[FunDef]
    
    def hasParent = !parent.isEmpty
  
    // Recursively gather all results of the given function from the top of the tree until this node (inclusive)
    def collectFromTop[T](fn : MemoClassRecord => T ) : Seq[T] = parent match {
      case None       => Seq(fn(this))
      case Some(prnt) => fn(this) +: prnt.collectFromTop[T](fn)
    }
    // Collect something according to fun from the whole tree below this node (inclusive)
    def collectFromTree[T](fn : MemoClassRecord => T ) : Seq[T] = {
      fn(this) +: ( children flatMap { _.collectFromTree(fn) } )
    }
    // Flat version of collectFromTree
    def flatCollectFromTree[T](fn : MemoClassRecord => Seq[T]) : Seq[T] = collectFromTree(fn).flatten

    // The new class definitions resulting from this tree
    def newClasses : Seq[ClassDef] = flatCollectFromTree { node => node.classDef +: node.extraField.toSeq } 
      
    // The new Functions resulting from this tree
    def newFunctions : Seq[FunDef] = flatCollectFromTree { node => node.fieldExtractor.toSeq ++ node.memoizedFuns }
          
    // The new constructors resulting from this tree
    def newConstructors : Seq[FunDef] = flatCollectFromTree { node => node.constructor.toSeq }

    

    

    // Make a method that retrieves the newly created fields from the new types
    // This function has to separate cases for the leaf types of this type
    lazy val fieldExtractor : Option[FunDef] = if (!hasLocalMemoFuns) None else Some({
      
      // Running example in the comments : say we start with a class called ClassName 

      // Name of resulting function e.g. getClassNameFields
      val funName = FreshIdentifier(s"get${extraField.get.id.name}")  
      // Type parameters of resulting function
      //val freshTpParams = freshenClassDefTpParams()
      //Use type parameters of classDef
      val tpParams = classDef.tparams map {_.tp}
      // Return type of res. function. e.g. ClassNameFields
      val retType = CaseClassType(extraField.get,tpParams) // FIXME OK
      // This will become a method, so use a ThisIdentifier
      val paramId = FreshThisId(classDefToClassType(classDef,tpParams)) // TODO
      // Arguments of resulting function, e.g. ( className : ClassName )
      val args = Seq(new ValDef(paramId, classType)) 

      // Body of resulting function
      val body: Expr = classDef match { 
        case cc : CaseClassDef =>
          // Here the body is just retrieving the field
          CaseClassSelector(new CaseClassType(cc, tpParams /*FIXME*/), Variable(paramId), cc.fields.find(_.id.name == funName.name).get.id)
        case ab : AbstractClassDef => {
          
          // Construct the cases :
          // The case classes on which we will match
          val caseClasses = this.caseDescendents map { _.classDef }  

          val cases = for (cc <- caseClasses) yield {
            val id = idToFreshLowerCase(cc.id)
            val patt = InstanceOfPattern( Some(id), new CaseClassType(cc, tpParams) )
            val bd = new CaseClassSelector( new CaseClassType(cc,tpParams /*FIXME*/), Variable(id),
              cc.fields.find( _.id.name == nameToLowerCase(extraField.get.id.name)).get.id
            )

            new SimpleCase(patt,bd)
          }


          // the variable to do case analysis on
          val scrutinee = Variable(paramId).setType(AbstractClassType(ab, tpParams)) // FIXME

          // The complete match expr.
          MatchExpr(scrutinee, cases)
        }
      }

      // Now construct the whole definition and add body
      val funDef = new FunDef(funName, classDef.tparams, retType, args) // FIXME type params
      funDef.body = Some(body)
      funDef.enclosing = Some(classDef) 
      funDef
      
    })

    // New versions of funsToMemoize, utilizing the memoized field
    lazy val memoizedFuns : Seq[FunDef] = for ( fn <- classDefRecursiveFuns) yield {
      // Use parent's type parameters, since this will become a method
      val tparams = classDef.tparams
      // Identifier of the input function
      assert( acceptableParams(fn) )
      val oldArg = fn.params.head.id
      // the new argument will have the new type corresponding to this type
      val newArg = new ValDef(freshIdentifier(oldArg.name), classType )
      val newArgs = if (fn.params.length > 1) Seq(newArg, fn.params(1))
                    else Seq(newArg)
      val newFun = new FunDef(
        id         = fn.id.freshen, 
        tparams    = tparams, // FIXME TYPE PARAMS
        returnType = fn.returnType, // This is correct only with side-effects
        params     = newArgs
      )
      // The object whose field we select is an application of fieldExtractor on newArg
      val argVar = Variable(newArg.id).setType(classType)
      val bodyObject = new FunctionInvocation( fieldExtractor.get.typed(tparams map {_.tp}), Seq(argVar) ) // FIXME Type params
      

      newFun.copyContentFrom(fn)
      
      newFun.body = Some(CaseClassSelector(
        CaseClassType(extraField.get, tparams map {_.tp}), // FIXME
        bodyObject, 
        extraField.get.fields.find{ _.id.name == fn.id.name }.get.id
      ))
      
      newFun.copiedFrom(fn)
    }


  }



  private case class MemoCaseClassRecord (
    p : Program,
    candidateFuns : Set[FunDef],
    classDef : CaseClassDef,
    parent : Option[MemoAbstractClassRecord]
  ) extends MemoClassRecord {
    
    type A = CaseClassDef
    
    val children: Seq[MemoClassRecord] = Seq()

    // Add all memoized functions from top of the tree as fields
    def enrichClassDef() {
      val allExtraFields = for (Some(cc) <- collectFromTop(_.extraField)) yield {  
        val newId = idToFreshLowerCase(cc.id)
        new ValDef(newId, CaseClassType(cc, freshenClassDefTpParams() ) ) //FIXME
      }
      if (!allExtraFields.isEmpty) {
        classDef.setFields( classDef.fields ++ allExtraFields )
        classDef.makeClass() //FIXME can this be corrected?
        extraFieldsNo = allExtraFields.length
      }
    }

  
    val constructor: Option[FunDef] = if (extraFieldsNo == 0) None else {        
      
      // The arguments of the new function. Correspond to the old fields of classDef  
      val args = for (field <- classDef.fields.take(classDef.fields.length - extraFieldsNo)) yield { 
        field.id.freshen.copiedFrom(field)
      }
     
      // Extra fields we are adding to classDef
      val extraCaseClasses : Seq[CaseClassDef] = 
        collectFromTop { _.extraField } collect { case Some(x) => x }
        
      /**
       * Functions corresponding to the extra fields
       */ 
      val extraFuns : Seq[Seq[FunDef]] = 
        collectFromTop { _.classDefRecursiveFuns } filter { !_.isEmpty }

      // The new vals we are going to be assigning the results of calling old function code into
      val assignedToVals : Seq[Seq[Identifier]] = for (cc <- extraCaseClasses) yield { 
        for (field <- cc.fields) yield {
          freshIdentifier(field.id.name + "_").copiedFrom(field)  
        }
      }

      val funsValsMap = (extraFuns.flatten zip assignedToVals.flatten).toMap 
      
      val freshTpParams = freshenClassDefTpParams()
      
      // Take an expression and isolate the case relevant for this constructor function
      // funArg is the argument of the original function
      // args are the arguments of the constructor function

      // FIXME: Does not work for TuplePatterns
      def isolateRelevantCases(fun : FunDef, args:Seq[Identifier])(expr : Expr) : Option[Expr] = {
        // The sole function argument
        val funArg = fun.params.head.id 
        // Relevant patterns are: 
        // Wildcard
        // CaseClassPattern with classDef
        // instanceOf with supertype of classDef
        def isRelevantPattern(pat: Pattern) : Boolean = pat match { 
          case WildcardPattern(_) => true
          case CaseClassPattern(_, cc, _) => cc.classDef == classDef
          case InstanceOfPattern(_, cc : CaseClassType) => cc.classDef == classDef
          case InstanceOfPattern(_, ab : AbstractClassType) => 
            ab.knownDescendents map { _.classDef } contains classDef
          case tp@TuplePattern(_,_) => 
            ctx.reporter.fatalError(
              tp.getPos + ":\n" +
              "TuplePatterns not supported yet!\n" + tp.toString
            ) //FIXME
        }


        expr match {
          case me@MatchExpr(Variable(id),cases) if (funArg == id) => { 
            val relCases = cases filter { mc => isRelevantPattern(mc.pattern) }
            // We will treat types with 0 fields separately
            if (args.size == 0){
              // Nothing to pattern match against, all patterns succeed. 
              // Guards have to be kept, but use if-then-else
              val relCases2 = relCases takeWhile { _.hasGuard }
              // Default of if-then-else will be first unguarded pattern, 
              // or an error if there is none
              val defaultExpr = 
                if (relCases2.length < relCases.length) relCases(relCases2.length).rhs
                else Error("Match Error: all guards failed while pattern matching against " +
                  "an object of class " + classDef.id.name
                ).setType(me.getType)

              def matchCaseToIfExpr( mc : MatchCase, expr : Expr ) : Expr = { 
                IfExpr(mc.theGuard.get, mc.rhs, expr)
              }
              Some( relCases2. :\ (defaultExpr)(matchCaseToIfExpr) )

            }

            else {

              // Keep only relevant cases. 
              // These will be either: 
              //    one instanceOf pattern, 
              //    or a wildcard, 
              //    or a series of caseClass or guarded patterns
              //      possibly followed by either a wildcard of InstanceOf 
              //      (which will then be "catch-all")
              val relCases2 = relCases takeWhile { cas => 
                cas.pattern.isInstanceOf[CaseClassPattern] || cas.hasGuard
              }
              val relevantCases = {
                if      (relCases.length == 1) relCases // One case
                else if (relCases.length == relCases2.length) relCases2 // All are CaseClassPatterns
                else    { 
                  // Neither of those. 
                  // Put all CaseClassPatterns/guarded patterns and a catch-all in the end
                  // The catch-all must have correct binder and 
                  val extraCase = relCases(relCases2.length) 
                  relCases2 :+ SimpleCase(WildcardPattern(extraCase.pattern.binder), extraCase.rhs)
                }
              }
              
              if (
                relevantCases.length == 1 && 
                relevantCases.head.pattern.isInstanceOf[CaseClassPattern] &&
                relevantCases.head.pattern.asInstanceOf[CaseClassPattern].subPatterns.forall {
                  _.isInstanceOf[WildcardPattern]
                }
              ) {
                // Special treatment:
                // No point pattern matching if there is only one case with these attributes
                val bdy     = relevantCases.head.rhs
                val thePatt = relevantCases.head.pattern.asInstanceOf[CaseClassPattern]
                val patts   = thePatt.subPatterns
                val binder  = thePatt.binder
                val vars    = args map Variable
                // We need to replace the subpatterns with the function arguments
                // and the binder with funArg
                val theMap1 = ( 
                  (patts zip vars) collect { 
                    case (patt,vr) if (patt.binder.isDefined) => (patt.binder.get, vr)
                  } 
                ).toMap 
                val theMap = 
                  if (binder.isDefined) theMap1 + (binder.get -> Variable(funArg))
                  else theMap1
                Some(replaceFromIDs( theMap, bdy))
              }
              else {

                // Reconstruct the MatchCase to remove funArg completely
                // The matched against expression will be a tuple with the fields of funArg
                def reconstructCase(mc: MatchCase, funArg : Identifier) : MatchCase = {
                  val newPattern = mc.pattern match {
                    // This always succeeds at this point
                    case InstanceOfPattern(binder, _) => WildcardPattern(binder)
                    case WildcardPattern  (binder)    => WildcardPattern(binder)
                    case CaseClassPattern(_, _, subPatterns) =>
                      assert(!subPatterns.isEmpty)
                      TuplePattern(None, subPatterns)
                    case tp@TuplePattern(_, _)  => //FIXME
                      ctx.reporter.fatalError("TuplePatterns not supported yet!\n" + tp.toString)
                  }

                  val newMc = mc match {
                    case SimpleCase (_,        rhs) => SimpleCase (newPattern,        rhs)
                    case GuardedCase(_, guard, rhs) => GuardedCase(newPattern, guard, rhs)
                  }

                  // If there is a binder, just replace it in all resulting expression with funArg
                  mc.pattern.binder match {
                    case None => newMc
                    case Some(binder) => {
                      def inCase(fn : Expr => Expr)(mc : MatchCase) = mc match {
                        case SimpleCase (pat,        rhs) => SimpleCase (pat,            fn(rhs))
                        case GuardedCase(pat, guard, rhs) => GuardedCase(pat, fn(guard), fn(rhs))
                      }
                      inCase(replaceFromIDs(Map(binder -> Variable(funArg)), _))(newMc)
                    }
                  }
                }
            
                val newScrut = Tuple(args map Variable)
                Some( MatchExpr(newScrut, relevantCases map {reconstructCase(_,funArg) } ))
              }
            }

          }

        
        
          case me@MatchExpr(tp@Tuple(_), cases ) if (variablesOf(tp) contains funArg) => {
/*
            var funDefIndexPaths : Seq[Seq[Int]] = Seq()

            def rec(ex : Expr, indexPath : Seq[Int]) = ex match {
              case Tuple(tupleArgs) => {
                val subTuples = for ((expr, ind) <- tupleArgs.zipWithIndex) yield {
                  rec(expr, indexPath :+ ind)
                }
                Tuple(subTuples)
              }
              case vr@Variable(id) if id == funArg => {
                funDefIndexPaths = funDefIndexPaths :+ indexPaths
                vr
              }
              case _ => isolateRelevantCases(funArg, args)(ex)
            }
            val isolated = rec(tp, Seq()) 
            funDefIndexPaths.length match {
              case 0 => Some( MatchExpr(isolated, cases))
              case 1 => 
                val indexPath = funDefIndexPaths.head

                // In the patterns, find the element corresponding to funDef
                def findPatt(patt : Pattern, indexPath : Seq[Int]) : Pattern  = {
                  patt match {
                    case Tuple(args) if !indexPath.isEmpty => 
                      findPatt(args(indexPath.head), indexPath.tail)
                    case _           if !indexPath.isEmpty => 
                      scala.sys.error("Paths don't match when searching for pattern position")
                    case _           if  indexPath.isEmpty => 
                      patt
                  }

                }

                val funDefPatts = for (cs <- cases) yield { findPatt(cs.pattern, indexPath) }
                ctx.reporter.fatalError("TuplePatterns not supported yet:\n" + tp.toString) //FIXME


              case _ => ctx.reporter.fatalError(me.getPos + ":\n" +
                "Cannot process MatchExpression with multiple instances of " + funDef.toString
              )
            }
*/
            ctx.reporter.fatalError("TuplePatterns not supported yet:\n" + tp.toString) //FIXME
          }

          case IfExpr(cond, thenn, elze) if (variablesOf(cond) contains funArg) =>
            // Try to simplify condition, based on the constructor simplifications 
            val newCond = isolateRelevantCases(fun,args)(cond)
            newCond match {
              case Some(BooleanLiteral(true)) => Some(thenn)
              case Some(BooleanLiteral(false)) => Some(elze)
              case Some(newCond) => Some(IfExpr(newCond,thenn,elze)) // Condition changed in some way
              case None => None // Condition did not change, return None so that preMap now descends deeper
            }
          

          case fi@FunctionInvocation(tfd, realArgs) if (realArgs contains Variable(funArg)) => {
            val funDef = tfd.fd
            
            if (extraFuns.flatten contains funDef) {
              // funDef is also being memoized, so use the variable it has been assigned to
              funsValsMap get funDef map Variable
            }
            else {
              assert(funDef.hasImplementation)
              // Check for possible unlimited unrolling...
              if ( p.callGraph.isRecursive(funDef) ) {
                ctx.reporter.fatalError(
                  s"${fi.getPos.toString}\n" +
                  s"Function ${fun.id.name} calls recursive function ${funDef.id.name}, which is not memoized.\n" +
                  s"Memoizing ${fun.id.name} would lead to multiple/unlimited unfolding of ${funDef.id.name}."
                )
              } else {
                // Unfold funDef once (replace formal params. with real)
                val unfolded = replaceFromIDs(funDef.params.map{_.id}.zip(realArgs).toMap, funDef.body.get)
                // Replace formal type parameters with real
                val theMap = (funDef.tparams zip tfd.tps).toMap
                Some (instantiateType(unfolded,theMap,Map()))
              }
            }
          }

          case CaseClassInstanceOf(cc, Variable(vr)) if (vr == funArg) =>
            Some(BooleanLiteral(cc.classDef == classDef)) 
        
          // If we are trying to get a field of funDef, 
          // we can just get the function argument in the same position
          case CaseClassSelector(ct, Variable(vr), id) if (vr == funArg) =>
            Some( Variable(args(ct.classDef.selectorID2Index(id)))) 

          // FIXME: Generally, we need to catch all expressions mentioning funArg
          //        Is there anything else to consider?
          
          // Let(_, ex, _ ) if (variablesOf(ex) contains funDef)
          // LetTuple(_, ex, _ ) if (variablesOf(ex) contains funDef)
          // TupleSelect
          // etc

          case vr@Variable(id) if (id == funArg) => {
            // This indicates failure to remove this instance of funDef early...
            ctx.reporter.fatalError(
              vr.getPos.toString + ":\n" + 
              "Failed to remove instance of variable " + id.name + "\n" +
              "while creating constructor function for class " + classDef.id.name
            )
          }

          case _ => None 
        }
      }
      
      // The expressions to be assigned to the new vals
      val assignedExprs : Seq[Seq[Expr]] = extraFuns map { 
        _ map { fun =>
          assert(fun.hasImplementation)
          assert(fun.tparams.length == freshTpParams.length)
          // First, instantiate function parameters in the function body
          val theMap = ( fun.tparams zip freshTpParams ).toMap
          val withFreshTypes = instantiateType(fun.body.get, theMap, Map()) 
          // Then apply isolateRelevantCases
          preMap(isolateRelevantCases(fun,args), true)(withFreshTypes) 
        }
      }

      // The expressions which will initialize the extra fields 
      val fieldInitializers : Seq[Expr] = for ( (cc,ids) <- extraCaseClasses zip assignedToVals ) yield {
        CaseClass(CaseClassType(cc, freshTpParams), ids map Variable)
      }
       
      // The final return value of the function
      val returnValue : Expr = CaseClass(
        CaseClassType(classDef, freshTpParams ), //FIXME
        (args map Variable) ++ fieldInitializers 
      )

      // Reorder value assignments to be in the correct dependency order
      // Found this here: https://gist.github.com/ThiporKong/4399695
      def topoSort[A](toPreds: Map[A,Set[A]]) : Seq[A] = {
        def tSort(toPreds: Map[A, Set[A]], done: Seq[A]): Seq[A] = {
          val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
          if (noPreds.isEmpty) {
            if (hasPreds.isEmpty) done else throw new IllegalArgumentException(
              s"Functions:\n ${noPreds mkString "\n"} \nare involved in circular definition!" 
            )
          } 
          else {
            val found : Seq[A] = noPreds.map{ _._1 }.toSeq
            tSort(hasPreds.mapValues { _ -- found }, found ++ done)    
          }
        }
        tSort(toPreds, Seq()).reverse
      }
      
      val valsWithExprs : Seq[(Identifier, Expr)] = assignedToVals.flatten zip assignedExprs.flatten
      val edges : Map[(Identifier,Expr),Set[(Identifier,Expr)]] = ( for ( (vl1, expr1) <- valsWithExprs) yield {
        (vl1, expr1) -> (valsWithExprs collect { 
          case (vl2, expr2) if (variablesOf(expr1) contains vl2) => (vl2,expr2)
        }).toSet 
      }).toMap
      val assignments: Seq[(Identifier, Expr)] = try {
        topoSort(edges)
      } 
      catch {
        // If the definitions have cycles, we output a program that won't compile
        // (but the original program looped anyway)
        case ex: IllegalArgumentException => 
          ctx.reporter.error(ex.getMessage())
          valsWithExprs
      }
       
      // Function to fold over all assignments to create body
      def makeLetDef( idValue : (Identifier, Expr) , bd : Expr) = Let(idValue._1, idValue._2, bd)  

      val body = assignments.  :\ (returnValue)(makeLetDef)

      val res = new FunDef(
        freshIdentifier("create" + classDef.id.name),
        freshTpParams map TypeParameterDef, // FIXME Type Params
        classType,
        for (arg <- args) yield { new ValDef(arg, arg.getType) }
      )
      
      res. body = Some(body)
      
      Some(res) 
    }


  }
  

  private case class MemoAbstractClassRecord (
    p : Program,
    candidateFuns : Set[FunDef],
    classDef : AbstractClassDef, 
    parent : Option[MemoAbstractClassRecord] 
  ) extends MemoClassRecord {
    
    type A = AbstractClassDef
    val constructor: Option[FunDef] = None
    
    // recursive! This is what actually constructs the trees
    val children : Seq[MemoClassRecord] = 
      classDef.knownChildren map { MemoClassRecord(p, candidateFuns, _, this) }

    def enrichClassDef() = { } 
  }


  private object MemoClassRecord {
    def apply(
      p: Program, 
      candidateFuns: Set[FunDef], 
      classDef : ClassDef
    ) : MemoClassRecord = classDef match {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, candidateFuns, ab, None)
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, candidateFuns, cc, None)
    }

    def apply(
      p: Program, 
      candidateFuns: Set[FunDef], 
      classDef : ClassDef, 
      parent : MemoAbstractClassRecord
    ) : MemoClassRecord = classDef match {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, candidateFuns, ab, Some(parent))
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, candidateFuns, cc, Some(parent))
    }

    def apply(
      p: Program, 
      candidateFuns: Set[FunDef], 
      classDef : ClassDef, 
      parent : Option[MemoAbstractClassRecord]
    ) : MemoClassRecord = classDef match {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, candidateFuns, ab, parent)
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, candidateFuns, cc, parent)
    }

  }

  
  // Take an Identifier and produce a fresh with lowewcase first letter
  private def idToFreshLowerCase (id : Identifier) = {
    assert(!id.name.isEmpty)
    freshIdentifier(nameToLowerCase(id.name))
  }
  
  private def nameToLowerCase(name : String ) = {
    assert(!name.isEmpty)
    name.updated(0, name(0).toLower)
  }

  
  /*
   * This is called in the end of transformation to fix expressions
   * Replaces:
   *  constructors of old case classes with new constructor functions
   *  old function invocation with new one
   *  matchings with an extra matching
   *
   * This is meant to be passed as an argument in preMap
   */

  private def repairExprAfterMemo(memoFunsMap : Map[FunDef,FunDef], constructorMap : Map[CaseClassDef, FunDef])(expr : Expr) : Option[Expr] = expr match {
    
    case CaseClass(CaseClassType(classDef,tps), args) if constructorMap contains classDef => {
      Some( FunctionInvocation(constructorMap.get(classDef).get.typed(tps), args) ) 
    }
    
    case FunctionInvocation(TypedFunDef(fd,tps),args) if memoFunsMap contains fd => {
      Some( FunctionInvocation(memoFunsMap.get(fd).get.typed(tps),args) ) 
    }
    
    case me : MatchExpr => { 
      
      var somethingChanged = false // avoid diverging preMap
      
      // Give a pattern an extra wildcard in the end, if needed (recursive)
      def fixPattern(p: Pattern) : Pattern = p match {
        case CaseClassPattern(binder,caseClassDef, subPatterns) =>
          // Side effects should ensure result of renewing type are visible here,
          // so add one wildcard for each additional field 
          val howManyExtraFields = caseClassDef.classDef.fields.length - subPatterns.length
          val newSubPatterns = (subPatterns map fixPattern) ++
            Seq.fill(howManyExtraFields){ WildcardPattern(None) }
          somethingChanged = (somethingChanged || howManyExtraFields > 0)
          CaseClassPattern(
            binder, 
            caseClassDef, 
            newSubPatterns
          )
          
        case TuplePattern(binder, subPatterns) => {
          assert(subPatterns.length > 0, "Tuple with 0 arguments") 
          TuplePattern(binder, subPatterns map fixPattern)
        }
        case _ => p          
      }
      
      def fixCase(mc : MatchCase) : MatchCase = mc match {
        case SimpleCase (patt,        rhs) => SimpleCase (fixPattern(patt),        rhs)
        case GuardedCase(patt, guard, rhs) => GuardedCase(fixPattern(patt), guard, rhs)
      }

      // construct the candidate new MatchExpr (side-effects!)
      val newMe = new MatchExpr(me.scrutinee, me.cases map fixCase)
      // Only return Some if something did change, to avoid diverging preMap
      if (somethingChanged) Some(newMe) else None
    }
    
    case _ => None
  }


  // Find which functions (may) need to get memoized
  private def findCandidateFuns(p: Program) : Set[FunDef]= {
    
    // All unproven VCs that we receive from the previous pipeline phases
    val unprovenVCs = p.definedFunctions flatMap {
      fn => fn.precondition.toSeq ++ fn.postcondition.toSeq.map {_._2}
    }
    dbg("I have these conditions")
    dbg( unprovenVCs map { con => 
      con.toString + "@" + con.getPos.toString 
    } mkString ("\n") )
    
    
    val referredFuns : Set[FunDef] = for (
      cond : Expr <- unprovenVCs.toSet;
      fi   <- functionCallsOf(cond)
    ) yield fi.tfd.fd
    dbg("Referred functions:\n" + referredFuns.map{_.id.name}.mkString("\n"))
    
    val transCalles = referredFuns flatMap p.callGraph.transitiveCallees
    dbg("Transitive callees:\n" + transCalles.map{_.id.name}.mkString("\n"))

    // The trans. closure of functions that are called from VCs 
    val allCandidates = transCalles ++ referredFuns ++  
      // ... and add the functions the user has annotated with forceMemo
      (p.definedFunctions filter { _.annotations.contains("forceMemo") } ).toSet
    dbg("I found these candidates:\n" + allCandidates.map {_.id.name}.mkString("\n"))
    
    
    
    
    // Filter these to have the desired form
    val recMemo = allCandidates filter { f =>  
      acceptableParams(f) &&
      f.params.head.getType.isInstanceOf[ClassType] &&
      p.callGraph.transitivelyCalls(f,f) &&
      ( 
        // TODO : clear out what happens in these cases.   
        if (f.returnType.isInstanceOf[ClassType]) { 
          val rootRet   = f.returnType.         asInstanceOf[ClassType].classDef.hierarchyRoot 
          val rootParam = f.params.head.getType.asInstanceOf[ClassType].classDef.hierarchyRoot 
          rootRet != rootParam
        }
        else true 
      )
    }
    
    // Every function that transitively calls a recursive function NOT in this list should be dropped
    val recNotMemo = p.definedFunctions.filter{ p.callGraph.isRecursive(_) }.toSet -- recMemo.toSet
    val toRet = recMemo -- p.callGraph.transitiveCallers(recNotMemo)
    
    for (fun <- recMemo -- toRet) {
      ctx.reporter.info(s"${fun.id.name} is not considered for memoization, as it is calling a non-memoized recursive function")
    }
    
    dbg("I found these final candidates:\n" + toRet.map {_.id.name}.mkString("\n"))
    
    toRet 
  }

  
  def apply(ctx: LeonContext, p : Program) : Program  = {

    this.ctx = ctx

   
    ctx.reporter.info("Applying memoization transformation on program")
    
    val candidateFuns = findCandidateFuns(p) 
    
    // The trees of the program class hierarchy
    val defTrees = p.classHierarchyRoots map { MemoClassRecord(p, candidateFuns , _) }
    
    // Map of (oldFun -> newFun). Will contain only funs that are memoized
    val memoFunsMap = ( for (
      tree  <- defTrees;
      funs1 <- tree collectFromTree {_.classDefRecursiveFuns} ;
      funs2 <- tree collectFromTree {_.memoizedFuns} ;
      fun   <- funs1 zip funs2
    ) yield fun ).toMap
    
    // The non-memoized functions 
    val nonMemoFuns = p.definedFunctions filter { fn => !(memoFunsMap contains fn) }

    // Map of type -> constructor. Only keep CaseClasses with constructors
    val constructorMap = ( for (
      tree <- defTrees;
      cc   <- tree.caseDescendents if cc.constructor.isDefined
    ) yield (cc.classDef, cc.constructor.get) ).toMap
    
    
    // A map which maps old definitions to new ones 
    var definitionsMap = Map[Definition, Seq[Definition]]()
    
    // New non-memo functions, compatible with new types function
    val newNonMemoFuns = for ( fn <- nonMemoFuns ) {
      definitionsMap += fn -> Seq(
        preMapOnFunDef(repairExprAfterMemo(memoFunsMap,constructorMap), true)(fn)
      )
    }
    
    // Currently no values allowed in top level, so nothing to do with them FIXME

    val classDefDefs = defTrees flatMap { _.collectFromTree { rec => 
      val extraField = rec.extraField.toSeq
      val fieldExt = rec.fieldExtractor.toSeq map preMapOnFunDef(repairExprAfterMemo(memoFunsMap,constructorMap), true)
      // Constructors get a special treatment, to not replace themselves into their own body
      val constr = rec.constructor.toSeq map { constr => 
        val ccd = constr.returnType.asInstanceOf[CaseClassType].classDef
        val newConstrMap = constructorMap - ccd
        preMapOnFunDef(repairExprAfterMemo(memoFunsMap,newConstrMap), true)(constr)
      }
      rec.classDef -> (rec.classDef +: ( extraField ++ fieldExt ++ constr)) } 
    }
    for (cl <- classDefDefs ) { definitionsMap += cl}
    
    val newMemoFuns = defTrees flatMap { _.collectFromTree { rec => 
      for ( (oldFun,newFun) <- rec.classDefRecursiveFuns zip rec.memoizedFuns ) yield {
        definitionsMap += oldFun -> Seq(
          preMapOnFunDef(repairExprAfterMemo(memoFunsMap,constructorMap), true)(newFun)
        )
      }
    }}
    
    

    // Make a new program containing the above definitions. 
    
    val newProg = new Program(p.id, for (m <- p.modules) yield {
      m.copy(defs = for(
        df <- m.defs;
        newDef <- definitionsMap.get(df).getOrElse(scala.sys.error(s"Did not find def. ${df.id.name} in map"))
      ) yield newDef )
    })
 
    // Hack : put everything in a module 
    new Program (p.id, List(ModuleDef(FreshIdentifier("standalone$"), newProg.modules flatMap {_.defs} )))

  }


}
