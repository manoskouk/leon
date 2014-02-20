package leon
package memoization

import leon._
import leon.utils._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Trees._
import purescala.Common._
import verification.VerificationReport
import verification.VerificationCondition
import utils._


object MemoizationPhase extends TransformationPhase {

  val name = "Memoization transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep Memoization information"
  override val definedOptions : Set[LeonOptionDef] = Set( 
    LeonFlagOptionDef("no-verify", "--no-verify", "Skip verification before memoization transformation."),
    LeonValueOptionDef("o",        "--o=<file>",  "Output file for memoization transformation.") 
  )

  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  

  // Identifier printing strategy 
  private val alwaysShowUniqueId = false 
  private def freshIdentifier (name : String) = FreshIdentifier(name, alwaysShowUniqueId)

  private abstract class MemoClassRecord[+A <: ClassDef](
    val p : Program,
    val candidateFuns : Set[FunDef],
    val classDef : A,
    val parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) {
    
    // Functions which recursively call themselves with their only argument being of type classDef
    val classDefRecursiveFuns : List[FunDef] = { candidateFuns filter { f =>
      f.params.head.getType.asInstanceOf[ClassType].classDef == classDef &&
      ( 
        // TODO : clear out what happens in these cases.   
        if (f.returnType.isInstanceOf[ClassType]) { 
          f.returnType.asInstanceOf[ClassType].classDef.hierarchyRoot != classDef.hierarchyRoot 
        }
        else true 
      )
    }}.toList
    val hasLocalMemoFuns = !classDefRecursiveFuns.isEmpty
    
    // Extra fields we are adding to the type. None if there is nothing to add
    val extraFieldAbstr : Option[AbstractClassDef] = {
      if (!hasLocalMemoFuns) None 
      else Some ( new AbstractClassDef(
        id = freshIdentifier(classDef.id + "FieldsAbstract"),
        tparams= Seq(), // FIXME
        parent = None
      ) )
    }
    val extraFieldConcr : Option[CaseClassDef] = {
      if (!hasLocalMemoFuns) None 
      else Some ({
        val concr = new CaseClassDef(
          id = freshIdentifier(classDef.id + "Fields"),
          tparams= Seq(), // FIXME
          parent = Some( AbstractClassType(extraFieldAbstr.get, Seq())), // FIXME type params?
          isCaseObject = false 
        )
        concr.setFields(classDefRecursiveFuns map { fn => 
          new ValDef(fn.id.freshen, fn.returnType) 
        })
        concr
      })
    }


    val children : List[MemoClassRecord[_]]
    lazy val descendents : List[MemoClassRecord[_]] = children match { 
      case Nil => Nil 
      case _   => children ++ (children flatMap { _.descendents })
    }
    
    lazy val caseDescendents = descendents filter { _.isLeaf }
    
    def isLeaf : Boolean = classDef match {
      case _ : CaseClassDef  => true
      case _                 => false
    }

    def classType = classDefToClassType(classDef)
    def hasParent = !parent.isEmpty
  
    // Recursively gather all results of the given function from the top of the tree
    def collectFromTop[A](fn : MemoClassRecord[_] => A ) : List[A] = parent match {
      case None       => List(fn(this))
      case Some(prnt) => fn(this) :: prnt.collectFromTop[A](fn)
    }
    // Collect something according to fun from the whole tree
    def collectFromTree[A](fn : MemoClassRecord[_] => A ) : List[A] = {
      fn(this) :: ( children flatMap { _.collectFromTree(fn) } )
    }

    // The new class definitions resulting from this tree
    def newClasses : List[ClassDef] = {
      val localDefs : List[ClassDef] =
        classDef :: List(extraFieldAbstr,extraFieldConcr).flatten
      localDefs ++ ( children flatMap { _.newClasses } )
    }
      
    // The new Functions resulting from this tree
    def newFuns : List[FunDef] = {
      val localDefs = fieldExtractor.toList ++ memoizedFuns
      localDefs ++ (children flatMap { _.newFuns } )
    }
    
    // The new constructors resulting from this tree
    def newConstructors : List[FunDef] = {
      val localDefs = constructor.toList 
      localDefs ++ (children flatMap { _.newConstructors } )
    }

    // How many fields were added to the class
    protected var extraFieldsNo = 0

    // Add all memoized functions from top of the tree as fields
    // Works with side effects!
    def enrichClassDef() : Unit
    enrichClassDef()
 
    // A new constructor for the caseclass type to make sure 
    // all fields are created with invariants
    val constructor: Option[FunDef]

    // Make a function that retrieves the newly created fields from the new types
    // This function has to separate cases for the leaf types of this type
    lazy val fieldExtractor : Option[FunDef] = if (!hasLocalMemoFuns) None else Some({
      
      // Running example in the comments : say we start with a class called ClassName 

      // Name of resulting function e.g. classNameFields
      val funName = idToFreshLowerCase(extraFieldConcr.get.id) 
      // Return type of res. function. e.g. ClassNameFields
      val retType = classDefToClassType(extraFieldConcr.get) 
      // Name of parameter e.g. className
      val paramName = idToFreshLowerCase(classDef.id)
      // Args of resulting function, e.g. ( className : ClassName )
      val args = List(new ValDef(paramName, classType)) 

      // Body of resulting function
      val body: Expr = classDef match { 
        case cc : CaseClassDef =>
          // Here the body is just retreiving the field
          //CaseClassSelector(cc, Variable(idToFreshLowerCase(cc.id)), funName)
          CaseClassSelector(new CaseClassType(cc, Seq() /*FIXME*/), Variable(paramName), cc.fields.find(_.id.name == funName.name).get.id)
        case ab : AbstractClassDef => {
          // Construct the cases :
          // The case classes on which we will match
          val caseClasses : List[CaseClassDef]= ( 
            this.caseDescendents map { _.classDef.asInstanceOf[CaseClassDef] } 
          )

          val cases = for (cc <- caseClasses) yield {
            val id = idToFreshLowerCase(cc.id)

            val patt = new CaseClassPattern( Some(id), new CaseClassType(cc, Seq() /*FIXME*/), 
              Seq.fill(cc.fields.length) (WildcardPattern(None))
            )

            val bd = new CaseClassSelector( new CaseClassType(cc,Seq() /*FIXME*/), Variable(id),
              cc.fields.find( _.id.name == funName.name ).get.id
            )

            new SimpleCase(patt,bd)
          }


          // the variable to do case analysis on
          val scrutinee = Variable(paramName).setType(classDefToClassType(ab))

          // The complete match expr.
          MatchExpr(scrutinee, cases)
        }
      }

      // Now construct the whole definition and add body
      val funDef = new FunDef(funName, Seq(), retType, args) // FIXME type params
      funDef.body = Some(body)
      
      //dbg(funDef.toString)
      funDef
    })

    // New versions of funsToMemoize, utilizing the memoized field
    lazy val memoizedFuns : List[FunDef] = classDefRecursiveFuns map { fn =>
      // Identifier of the input function
      val oldArg = fn.params.head.id
      // the new argument will have the new type corresponding to this type
      val newArg = new ValDef(freshIdentifier(oldArg.name), classType )
      val newFun = new FunDef(
        id = freshIdentifier(fn.id.name), // FIXME use freshen
        Seq(), // FIXME TYPE PARAMS
        returnType = fn.returnType, // This is correct only with side-effects
        params = List(newArg)
      )
      // The object whose field we select is an application of fieldExtractor on newArg
      val argVar = Variable(newArg.id).setType(classType)
      val bodyObject = new FunctionInvocation( fieldExtractor.get.typed(Seq()), List(argVar) ) // FIXME Type params
      newFun.body = Some(CaseClassSelector(
        CaseClassType(extraFieldConcr.get, Seq()), // FIXME
        bodyObject, 
        extraFieldConcr.get.fields.find{ _.id.name == fn.id.name }.get.id
      ))

      newFun
    }


  }



  private class MemoCaseClassRecord (
    p : Program,
    candidateFuns : Set[FunDef],
    classDef : CaseClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) extends MemoClassRecord[CaseClassDef](p,candidateFuns,classDef,parent) {
    
    val children: List[MemoClassRecord[CaseClassDef]] = Nil

    // Add all memoized functions from top of the tree as fields
    def enrichClassDef() : Unit = {
      val allExtraFields = collectFromTop(_.extraFieldConcr).flatten map { cc => 
        val newId = idToFreshLowerCase(cc.id)
        new ValDef(newId, classDefToClassType(cc) )
      }
      if (!allExtraFields.isEmpty) {
        classDef.setFields( classDef.fields ++ allExtraFields )
        extraFieldsNo = allExtraFields.length
      }
    }

  
    val constructor: Option[FunDef] = if (extraFieldsNo == 0) None else {        
      
      // The arguments of the new function. Correspond to the old fields of classDef  
      val args = classDef.fields.take(classDef.fields.length - extraFieldsNo) map { 
        field => field.id.freshen.setType(field.tpe)
      }
     
      // Extra fields we are adding to classDef
      val extraCaseClasses : List[CaseClassDef] = 
        collectFromTop { _.extraFieldConcr } collect { case Some(x) => x }
      // Functions corresponding to the extra fields
      val extraFuns : List[List[FunDef]] = //FIXME
        collectFromTop { _.classDefRecursiveFuns } filter { !_.isEmpty }

      // The new vals we are going to be assigning the results of calling old function code into
      val assignedToVals : List[List[Identifier]] = extraCaseClasses map { 
        _.fields.toList map { field =>
          freshIdentifier(field.id.name + "_").setType(field.getType) 
          // TODO: WHY DOES VARDECL OVERRIDE GETTYPE? :'(
        }
      }

      val funsValsMap = (extraFuns.flatten zip assignedToVals.flatten).toMap 

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
            ab.knownDescendents contains classDef
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
                      // (Subpatterns should not be empty here)
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


          case fi@FunctionInvocation(tfd, realArgs) if (realArgs contains Variable(funArg)) => {
            val funDef = tfd.fd
            // funDef is also being memoized, so use the variable it has been assigned to
            if (extraFuns exists (_ contains funDef)) { //FIXME slow
              funsValsMap get funDef map Variable
            }
            else {
              // Check for possible unlimited unrolling...
              if ( p.callGraph.isRecursive(tfd.fd) ) {
                ctx.reporter.fatalError(
                  fi.getPos.toString + ":\n" +
                  "Function " + fun.id.name + " calls recursive function " + funDef.id.name + 
                  ", which is not memoized.\n " +
                  "Memoizing " + fun.id.name + " would lead to multiple/unlimited unfolding of " + funDef.id.name
                )
              } else {
                // Unfold funDef once (replace formal with real args)
                Some( replaceFromIDs(funDef.params.map{_.id}.zip(realArgs).toMap, funDef.body.get) )
              }

            }
          }

          case IfExpr(cond,thenn, elze) => None // Fixme: we may have to drop a branch, as in match
          case CaseClassInstanceOf(cc, Variable(vr)) if (vr == funArg) =>
            // TODO: Why only caseclass?
            Some(BooleanLiteral(cc == classDef)) 
        
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
      val assignedExprs : List[List[Expr]] = extraFuns map { 
        _ map { fun =>
          preMap(isolateRelevantCases(fun,args), true)(fun.body.get) 
        }
      }

      // The expressions which will initialize the extra fields 
      val fieldInitializers : List[Expr] = (extraCaseClasses zip assignedToVals) map {
        case (cc, ids) => CaseClass(CaseClassType(cc, Seq() /*FIXME*/), ids map Variable)
      }
       
      // The final return value of the function
      val returnValue : Expr = CaseClass(
        CaseClassType(classDef, Seq() ), //FIXME
        (args map Variable) ++ fieldInitializers 
      )

      // Reorder value assignments to be in the correct dependency order
      // Found this here: https://gist.github.com/ThiporKong/4399695
      def topoSort[A](toPreds: Map[A,Set[A]]) : List[A] = {
        def tSort(toPreds: Map[A, Set[A]], done: List[A]): List[A] = {
          val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
          if (noPreds.isEmpty) {
            if (hasPreds.isEmpty) done else throw new IllegalArgumentException(
              "Functions:\n" ++ (noPreds mkString "\n" ) ++ "\nare involved in circular definition!" 
            )
          } 
          else {
            val found : List[A] = noPreds.map { _._1 }.toList
            tSort(hasPreds.mapValues { _ -- found }, found ++ done)    
          }
        }
        tSort(toPreds, List()).reverse
      }
      val valsWithExprs : List[(Identifier, Expr)] = assignedToVals.flatten zip assignedExprs.flatten
      val edges : Map[(Identifier,Expr),Set[(Identifier,Expr)]] = ( 
        valsWithExprs map { case (vl1, expr1) =>
          (vl1, expr1) -> (valsWithExprs collect { 
            case (vl2, expr2) if (variablesOf(expr1) contains vl2) => (vl2,expr2)
          }).toSet 
        }
      ).toMap
      val assignments: List[(Identifier, Expr)] = try {
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
        Seq(), // FIXME Type Params
        classType,
        args map { arg => new ValDef(arg, arg.getType) }
      )
      
      res. body = Some(body)
      Some(res)
    }


  }
  

  private class MemoAbstractClassRecord (
    p : Program,
    candidateFuns : Set[FunDef],
    classDef : AbstractClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) extends MemoClassRecord[AbstractClassDef](p,candidateFuns,classDef,parent) {
    
    val constructor: Option[FunDef] = None
    
    // recursive! 
    val children : List[MemoClassRecord[ClassDef]] = 
      classDef.knownChildren.toList map { cd => MemoClassRecord(p, candidateFuns, cd, this) }

    def enrichClassDef = { } 
  }


  private object MemoClassRecord {
    def apply(
      p: Program, 
      candidateFuns: Set[FunDef], 
      classDef : ClassDef
    ) : MemoClassRecord[ClassDef] = classDef match {
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
    ) : MemoClassRecord[ClassDef] = classDef match {
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
    ) : MemoClassRecord[ClassDef] = classDef match {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, candidateFuns, ab, parent)
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, candidateFuns, cc, parent)
    }

  }

  
  // Take an Identifier and produce a fresh with lowewcase first letter
  private def idToFreshLowerCase (id : Identifier) = {
    val nm = id.name
    freshIdentifier(nm.updated(0,nm.head.toLower))
  }

  /*
   * Replace:
   *
   *  constructors of old case classes with new constructor functions
   *
   * This is meant to be passed as an argument in preMap
   */

  private def replaceConstructors(constructorMap : Map[CaseClassDef, FunDef])(expr : Expr) : Option[Expr] = expr match {
    case CaseClass(classTp, args) => constructorMap get classTp.classDef match {
      case None         => None 
      case Some(constr) => Some( new FunctionInvocation(constr.typed, args) ) //FIXME
    }
    case _ => None
  }

  /*
   * Replace:
   *
   *  old function invocation with new one
   *  matchings with an extra matching
   *
   * This is meant to be passed as an argument in preMap
   */

  private def replaceFunsAndPatternMatching(memoFunsMap : Map[FunDef,FunDef])(expr : Expr) : Option[Expr] = expr match {
    case FunctionInvocation(tfd,args) => 
      memoFunsMap get tfd.fd match {
        case None        => None
        case Some(newFn) => 
          Some(FunctionInvocation(newFn.typed,args)) //FIXME
      }
    
    case me : MatchExpr => 
      
      var somethingChanged = false // avoid diverging preMap
      
      // Give a pattern an extra wildcard in the end, if needed (recursive)
      def fixPattern(p: Pattern) : Pattern = p match {
        case CaseClassPattern(binder,caseClassDef, subPatterns) =>
          // Side effects should ensure result of renewing type are visible here,
          // so add one wildcard for each additional field 
          somethingChanged = caseClassDef.fields.length != subPatterns.length
          val newSubPatterns = (subPatterns map fixPattern) ++
            Seq.fill(caseClassDef.fields.length - subPatterns.length){ WildcardPattern(None) }
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
      if (somethingChanged) Some(newMe) else None
     
    case _ => None
  }


  private def replOnFunDef(repl : Expr => Option[Expr], applyRec : Boolean = false )(fn : FunDef) : FunDef = {

    def sar (ex : Expr ) : Expr = preMap(repl, applyRec)(ex)

    val newBody = sar(fn.body.get)
    val newFun = new FunDef(fn.id, Seq(), fn.returnType, fn.params) // FIXME type params
    newFun.body = Some(newBody)
    newFun.precondition  = fn.precondition  map sar
    newFun.postcondition = fn.postcondition map { case (id, ex) => (id, sar(ex)) }
    newFun
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
    
    
    val referredFuns : Set[FunDef] = //unprovenVCs flatMap functionCallsOf map { _.funDef }
      for (
        cond: Expr <- unprovenVCs.toSet;
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
    val toRet = allCandidates filter { f =>  
      f.params.size == 1 &&
      f.params.head.getType.isInstanceOf[ClassType] &&
      p.callGraph.transitivelyCalls(f,f) 
    }
    dbg("I found these final candidates:\n" + toRet.map {_.id.name}.mkString("\n"))
    
    toRet 
  }

  def apply(ctx: LeonContext, p : Program) : Program  = {

    this.ctx = ctx

    var outputFile : String = "memo.out.scala" 
    for (opt <- ctx.options) opt match {
      case LeonValueOption("o", file) =>
        outputFile = file 
      case _ => 
    }

    ctx.reporter.info("Applying memoization transformation on program " + p.id.name)
    
    val candidateFuns =   findCandidateFuns(p) //vRep)
    val defTrees = p.classHierarchyRoots.toList map { cd => MemoClassRecord(p, candidateFuns , cd) }
    
    // Map of (oldFun -> newFun). Will contain only funs that are memoized
    val memoFunsMap = defTrees.flatMap { _.collectFromTree( 
      rec => rec.classDefRecursiveFuns zip rec.memoizedFuns
    )}.flatten.toMap
    
    // The non-memoized functions 
    val nonMemoFuns = p.definedFunctions filter { fn => 
      ( memoFunsMap get fn).isEmpty
    }

    // Map of type -> constructor. only keep CaseClasses with constructors
    val constructorMap : Map[CaseClassDef, FunDef] = defTrees.flatMap { 
      _.collectFromTree { rec => (rec.classDef, rec.constructor) }
    }.collect { case (cc, Some(constr)) => (cc.asInstanceOf[CaseClassDef], constr)
    }.toMap
    

    // New non-memo functions, compatible with new types function
    val newNonMemoFuns = ( nonMemoFuns 
      map replOnFunDef(replaceFunsAndPatternMatching(memoFunsMap))
      map replOnFunDef(replaceConstructors(constructorMap))
    )
    
    // Currently no values allowed in toplevel, so nothing to do with them

    val newClasses = defTrees flatMap { _.newClasses }
    val newFuns    = ( defTrees flatMap { _.newFuns } 
      map replOnFunDef(replaceFunsAndPatternMatching(memoFunsMap))
      map replOnFunDef(replaceConstructors(constructorMap))
    )
    
    // Constructors get a special treatment, to not replace themselves into their own body
    val newConstructors = ( defTrees flatMap { _.newConstructors } 
      map replOnFunDef(replaceFunsAndPatternMatching(memoFunsMap))
      map { con => replOnFunDef(replaceConstructors(constructorMap - con.returnType.asInstanceOf[CaseClassType].classDef))(con) }
    )

    // Make a new program containing the above definitions. 
    val progName = freshIdentifier(p.modules.head.id.name + "Expanded") // FIXME find a better name
    val newProg = new Program(progName, List(ModuleDef(
      progName,
      newNonMemoFuns ++ newClasses ++ newFuns ++ newConstructors//, 
      //p.mainModule.invariants map 
      //  preMap(replaceFunsAndPatternMatching(memoFunsMap)) map 
      //  preMap(replaceConstructors(constructorMap))
    )))

    newProg.writeScalaFile(outputFile)

    newProg

  }


}
