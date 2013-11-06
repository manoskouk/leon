package leon
package Memoization

import leon._
import leon.utils._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Trees._
import purescala.Common._

object MemoizationPhase extends TransformationPhase {
  val name = "Memoization transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep Memoization information"


  abstract class MemoClassRecord[+A <: ClassTypeDef](
    val p : Program,
    val classDef : A,
    val parent : Option[MemoClassRecord[AbstractClassDef]] 
  )  { 
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
    def newClasses : List[ClassTypeDef] = {
      val localDefs : List[ClassTypeDef] =
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

    protected var hasExtraFields = false


    // Functions which recursively call themselves with their only argument being of type classDef
    val classDefRecursiveFuns : List[FunDef] = p.definedFunctions.toList filter { f => 
      p.transitivelyCalls(f,f) &&
      f.args.size == 1 &&
      f.args.head.getType.asInstanceOf[ClassType].classDef == classDef
    } 

    // Add all memoizes functions from top of the tree as fields
    def enrichClassDef() : Unit 

    enrichClassDef()


       
    val hasLocalMemoFuns = !classDefRecursiveFuns.isEmpty


    // New versions of funsToMemoize, utilizing the memoized field
    def memoizedFuns : List[FunDef] = classDefRecursiveFuns map { fn =>
      // Identifier of the input function
      val oldArg = fn.args.head.id
      // the new argument will have the new type corresponding to this type
      val newArg = new VarDecl(FreshIdentifier(oldArg.name), classType ) // richType)
      val newFun = new FunDef(
        id = FreshIdentifier(fn.id.name),
        returnType = fn.returnType, // FIXME!!! need to search for the new type corresponding to the old one
        args = List(newArg)
      )
      // The object whose field we select is an application of fieldExtractor on newArg
      val argVar = Variable(newArg.id)
      argVar.setType(classType)//richType)
      val bodyObject = new FunctionInvocation( fieldExtractor.get, List(argVar) )
      newFun.body = Some(CaseClassSelector(
        extraFieldConcr.get, 
        bodyObject, 
        extraFieldConcr.get.fields.find{ _.id.name == fn.id.name }.get.id
      ))

      newFun
    }

   

    // Extra fields we are adding to the type. None if there is nothing to add
    lazy val extraFieldAbstr : Option[AbstractClassDef] = {
      if (!hasLocalMemoFuns) None 
      else Some ( new AbstractClassDef(id = FreshIdentifier(classDef.id + "FieldsAbstract")) )
    }
    lazy val extraFieldConcr : Option[CaseClassDef] = {
      if (!hasLocalMemoFuns) None 
      else Some ({
        val concr = new CaseClassDef(id = FreshIdentifier(classDef.id + "Fields") )
        concr.setParent(extraFieldAbstr.get)
        concr.fields = classDefRecursiveFuns map { fn => new VarDecl(fn.id.freshen, fn.returnType) } 
        concr
      })
    }

    // A new constructor for the caseclass type to make sure 
    // all fields are created with invariants
    val constructor: Option[FunDef]

    

    // Make a function that retrieves the newly created fields from the new types
    // This function has to separate cases for the leaf types of this type
    def fieldExtractor : Option[FunDef] = if (!hasLocalMemoFuns) None else Some({
      
      // Running example in the comments : say we start with a class called ClassName 

      // Name of resulting function e.g. classNameFields
      val funName = idToLowerCase(extraFieldConcr.get.id) 
      // Return type of res. function. e.g. ClassNameFields
      val retType = classDefToClassType(extraFieldConcr.get) 
      // Name of parameter e.g. className
      val paramName = idToLowerCase(classDef.id)
      // Args of resulting function, e.g. ( className : ClassName )
      val args = List(new VarDecl(paramName, classType)) //richType)) // classDefToClassType(richClassDef)))

      // Body of resulting function
      val body: Expr = classDef match { // richClassDef match { // FIXME changed to rich
        case cc : CaseClassDef =>
          // Here the body is just retreiving the field
          CaseClassSelector(cc, Variable(idToLowerCase(cc.id)), funName)
        case ab : AbstractClassDef => {
          // Construct the cases :
          // The case classes on which we will match
          val caseClasses : List[CaseClassDef]= ( this.caseDescendents 
            //map { _.richClassDef.asInstanceOf[CaseClassDef] } 
            map { _.classDef.asInstanceOf[CaseClassDef] } 
          )
          // Case patterns
          val patterns = caseClasses map { cc => 
            new CaseClassPattern( 
              binder       = Some(idToLowerCase(cc.id)),
              caseClassDef = cc,
              // this is a dodgy way to create repeated "_"s of the correct size
              subPatterns  = cc.fields map (_ => new WildcardPattern(None))
            )
          }
          // case bodies
          val caseBodies = caseClasses map { cc => 
            //dbg(cc.toString)
            //dbg(funName.name)
            new CaseClassSelector(
              cc, 
              Variable(idToLowerCase(cc.id)), // FIXME maybe needs the pattern binder
              cc.fields.find( _.id.name == funName.name ).get.id
            )
          }
          
          // complete cases
          val cases = (patterns zip caseBodies) map { case (patt, bd) => new SimpleCase(patt, bd) }

          // the variable to do case analysis on
          val scrutinee = Variable(paramName)
          scrutinee.setType(classDefToClassType(ab))

          // The complete match expr.
          MatchExpr(scrutinee, cases)
        }
      }

      // Now construct the whole definition and add body
      val funDef = new FunDef(funName, retType, args)
      funDef.body = Some(body)
      
      //dbg(funDef.toString)
      funDef
    })



  }

  class MemoCaseClassRecord (
    p : Program,
    classDef : CaseClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) extends MemoClassRecord[CaseClassDef](p,classDef,parent) {
    
    val children: List[MemoClassRecord[CaseClassDef]] = Nil
       
    //val richClassDef: CaseClassDef = 

    // Add all memoizes functions from top of the tree as fields
    def enrichClassDef() : Unit = { 
      val allExtraFields = collectFromTop(_.extraFieldConcr).flatten.map{varFromClassDef(_)}
      if (allExtraFields.isEmpty) { }   
      else {
        classDef.fields = classDef.fields ++ allExtraFields
        hasExtraFields = true
      }
    }

  
    val constructor: Option[FunDef] = { 
      if (!hasExtraFields) None 
      else {        
        
        // The arguments of the new function. Correspond to the old fields of classDef  
        val args = classDef.fields.take(classDef.fields.length - 1) map { 
          arg => new VarDecl(arg.id.freshen, arg.tpe) 
        }
       
        // Extra fields we are adding to classDef
        val extraCaseClasses : List[CaseClassDef] = 
          collectFromTop { _.extraFieldConcr } filter { _.isDefined } map { _.get }

        // Functions corresponding to the extra fields
        val extraFuns : List[List[FunDef]] = 
          collectFromTop { _.classDefRecursiveFuns } filter { !_.isEmpty }

        // The new vals we are going to be assigning the results of calling old function code into
        val assignedToVals : List[List[Identifier]] = extraCaseClasses map { 
          _.fields.toList map { field =>
            val id = FreshIdentifier(field.id.name + "_")
            id.setType(field.getType) // TODO: WHY DOES VARDECL OVERRIDE GETTYPE? :'(
            id
          }
        }

        val funsValsMap = (extraFuns.flatten zip assignedToVals.flatten).toMap 

        // Take an expression and isolate the case relevant for this constructor function
        // funArg is the argument of the original function
        // args are the arguments of the constructor function
        def isolateCase(expr: Expr, funArg : Identifier, args:VarDecls) : Option[Expr] = expr match {
          case MatchExpr(vr@Variable(id),cases) if (funArg == id) => { 
            

            // Relevant patterns are: 
            // Wildcard
            // CaseClassPattern with classDef
            // instanceOf with supertype of classDef

            def hasRelevantPattern(mc : MatchCase) : Boolean = mc.pattern match { 
              case WildcardPattern(_) => true
              case CaseClassPattern(_, cc, subPatts) => cc == classDef
              case InstanceOfPattern(_, cc@CaseClassDef(_,_,_))   => cc == classDef
              case InstanceOfPattern(_, ab@AbstractClassDef(_,_)) => ab.knownDescendents contains classDef
              case _ => false
            } //FIXME
          
            // Now keep only relevant cases. 
            // These will be either: 
            //    one instanceOf pattern, 
            //    or a wildcard, 
            //    or a series of caseClass or guarded patterns
            //      possibly followed by either a wildcard of InstanceOf (which will then be "catch-all")
            val relCases = cases filter hasRelevantPattern 

            val relCases2 = relCases takeWhile { cas => 
              cas.pattern.isInstanceOf[CaseClassPattern] || cas.hasGuard
            }
             
            val relevantCases = {
              if      (relCases.length == 1) relCases // One case
              else if (relCases.length == relCases2.length) relCases2 // All are CaseClassPatterns
              else    { // Neither of those. Put all CaseClassPatterns and a catch-all in the end
                val extraCase = relCases(relCases2.length) 
                relCases2 :+ SimpleCase(WildcardPattern(extraCase.pattern.binder), extraCase.rhs)
                // FIXME : guards not handled properly!!!
              }
            }

            // Unfold a MatchCase 
            // constrArgs are the arguments of the constructor function
            // Partially implemented FIXME 
            def unfoldCase(mc: MatchCase, constrArgs: VarDecls) : MatchCase = mc match {
              case SimpleCase(CaseClassPattern(None, _, subPatts), rhs) => 
                val newPatt = TuplePattern(None, subPatts)
                SimpleCase(newPatt, rhs) 
              case _ => scala.sys.error("unfoldCase partially implemented")
                              
            }
            
            if (args.size == 0 ) {
              Some(relevantCases.head.rhs) // FIXME
            }
            else {
              val newScrut = Tuple(args map { arg => Variable(arg.id) })
              Some( MatchExpr(newScrut, relevantCases map {unfoldCase(_, args)}) )// FIXME: this works for CaseClassPatterns only
            }

          }

          case MatchExpr(Tuple(_),_) => None // FIXME!!!
          
          // FIXME: Generally, we need to catch all expressions mentioning funArg
          case FunctionInvocation(funDef, args_) if (args_ contains Variable(funArg)) => {
            
            if (extraFuns exists (_ contains funDef)) { //FIXME slow
              funsValsMap get funDef map Variable
            }
            else {
              // Isolate the case in the old body function
              val isolatedBody = //funDef.body.get
                searchAndReplace(x=> isolateCase(x,funDef.args.head.id,args))( funDef.body.get) // FIXME : correct parameters in isolateCase???
              // Let value is isolated funbody, but replace typical parameters with actual
              val letValue = replaceFromIDs( 
                ( funDef.args.map{ _.id } zip args.map{arg => Variable(arg.id)}).toMap,
                isolatedBody 
              )
              Some(letValue)
            }

          }
          case _ => None 
        }
        
        // The expressions to be assigned to the new vals
        val assignedExprs : List[List[Expr]] = extraFuns map { 
          _ map { fun =>
            searchAndReplace(x => isolateCase(x,fun.args.head.id,args))(fun.body.get) 
          }
        }

        // The expressions which will initialize the extra fields 
        val fieldInitializers : List[Expr] = (extraCaseClasses zip assignedToVals) map {
          case (cc, ids) => CaseClass(cc, ids map { id => Variable(id) })
        }
         
        // The final return value of the function
        val returnValue : Expr = CaseClass(
          classDef, 
          (args map { arg => Variable(arg.id) }) ++ fieldInitializers 
        )
        dbg("CASE CLASS APP")
        dbg(returnValue.toString)
        // Function to fold over all assignments to create body
        def makeLetDef( idValue : (Identifier, Expr) , bd : Expr) = Let(idValue._1, idValue._2, bd)  

        val body = ( assignedToVals.flatten zip assignedExprs.flatten ). :\ (returnValue)(makeLetDef)

        val res = new FunDef(
          FreshIdentifier("create" + classDef.id.name),
          classType,
          args 
        )
        
        res. body = Some(body)
        Some(res)

      }
    }
  }
  

  class MemoAbstractClassRecord (
    p : Program,
    classDef : AbstractClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) extends MemoClassRecord[AbstractClassDef](p,classDef,parent) {
    
    val constructor: Option[FunDef] = None
    
    // recursive! 
    val children : List[MemoClassRecord[ClassTypeDef]]= classDef.knownChildren.toList map {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, ab, Some(this))
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, cc, Some(this))
    }


    def enrichClassDef = { } 
  }



  implicit val debugSection = DebugSectionMemoization

  var ctx : LeonContext = null
  def dbg(x:String) = ctx.reporter.debug(x)
  

  

  // Take a ClassTypeDef and make a field with the same name (lower-case) 
  // and the correct type
  def varFromClassDef(cc : ClassTypeDef) : VarDecl = {
    val newId = idToLowerCase(cc.id)
    new VarDecl(newId, classDefToClassType(cc) )
  }

  // Take an Identifier and produce a fresh with lowewcase first letter
  def idToLowerCase (id : Identifier) = {
    val nm = id.name
    FreshIdentifier(nm.updated(0,nm.head.toLower))
  }

  /*
   * Replace:
   *
   *  constructors of old case classes with new constructor functions
   *
   * This is meant to be passed as an argument in searchAndReplace
   */

  def replaceConstructors(
    expr: Expr, 
    constructorMap : Map[CaseClassDef, FunDef]
  ) : Option[Expr] = expr match {
    case CaseClass(classDef, args) => constructorMap get classDef match {
      case None         => None 
      case Some(constr) => Some( new FunctionInvocation(constr, args) )
    }
    case _ => None
  }

  /*
   * Replace:
   *
   *  old function invocation with new one
   *  matchings with an extra matching
   *
   * This is meant to be passed as an argument in searchAndReplace
   */

  def replaceFunsAndPatternMatching ( 
    expr : Expr, 
    memoFunsMap : Map[FunDef,FunDef]
  ) : Option[Expr] = expr match {
    case FunctionInvocation(funDef,args) => 
      memoFunsMap get funDef match {
        case None        => None
        case Some(newFn) => Some(FunctionInvocation(newFn,args))
      }
    
    case me : MatchExpr => 
      // Give a pattern an extra wildcard in the end, if needed (recursive)
      def fixPattern(p: Pattern) : Pattern = p match {
        case CaseClassPattern(binder,caseClassDef, subPatterns) =>
          // Side effects should ensure result of renewing type are visible here
          if (caseClassDef.fields.length == subPatterns.length) p
          else 
            CaseClassPattern(
              binder, 
              caseClassDef, 
              (subPatterns map fixPattern) :+ WildcardPattern(None)
            )
        case TuplePattern(binder, subPatterns) => TuplePattern(binder, subPatterns map fixPattern)
        case _ => p          
      }
      
      def fixCase(mc : MatchCase) : MatchCase = mc match {
        case SimpleCase (patt,        rhs) => SimpleCase (fixPattern(patt),        rhs)
        case GuardedCase(patt, guard, rhs) => GuardedCase(fixPattern(patt), guard, rhs)
      }

      Some( new MatchExpr(me.scrutinee, me.cases map fixCase) )
     
    case _ => None
  }


  def applyReplacementOnFunDef(repl : Expr => Option[Expr])(fn : FunDef) : FunDef = {

    def sar (ex : Expr ) : Expr = searchAndReplace(repl)(ex)

    val newBody = sar(fn.body.get)
    val newFun = new FunDef(fn.id, fn.returnType, fn.args)
    newFun.body = Some(newBody)
    newFun.precondition  = fn.precondition  map sar
    newFun.postcondition = fn.postcondition map { case (id, ex) => (id, sar(ex)) }
    newFun
  }



  def apply (ctx: LeonContext, p: Program) = {

    def dbg(x:Any) = ctx.reporter.debug(x.toString)
    this.ctx = ctx

    //this.ctx = ctx
    ctx.reporter.info("Hello Memoization!")
      
    val defTrees = p.classHierarchyRoots.toList map { 
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, ab, None)
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, cc, None)
    }

   
    
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
    }.filter { _._2.isDefined }.map {
      case (cc, Some(constr)) => (cc.asInstanceOf[CaseClassDef], constr)
    }.toMap
      

    // New non-memo functions, compatible with new types function
    val newNonMemoFuns = nonMemoFuns map {
      applyReplacementOnFunDef(ex => replaceFunsAndPatternMatching(ex,  memoFunsMap))
    } map {
      applyReplacementOnFunDef(ex => replaceConstructors(ex,  constructorMap))
    }
    // Currently no values allowed in toplevel, so nothing to do with them

    val newClasses = defTrees flatMap { _.newClasses }
    val newFuns    = defTrees flatMap { _.newFuns } map {
      applyReplacementOnFunDef(ex => replaceFunsAndPatternMatching(ex,  memoFunsMap))
    } map {
      applyReplacementOnFunDef(ex => replaceConstructors(ex,  constructorMap))
    }

    
    val newConstructors = defTrees flatMap { _.newConstructors } map {
      applyReplacementOnFunDef(ex => replaceFunsAndPatternMatching(ex,  memoFunsMap))
    }

    /*
    // DEBUGGING!
    newClasses map dbg 
    newFuns map dbg
    newNonMemoFuns map dbg
    */

    // Make a new program containing the above definitions. 
    val progName = FreshIdentifier(p.mainObject.id.name + "Expanded")
    val newProg = Program(progName, ObjectDef(
      progName,
      newNonMemoFuns ++ newClasses ++ newFuns ++ newConstructors, 
      p.mainObject.invariants map { searchAndReplace( 
        ex => replaceFunsAndPatternMatching(ex,  memoFunsMap)
      )} map { searchAndReplace(
        ex => replaceConstructors(ex,  constructorMap)
      )}
    ))

    // FIXME: REMOVE HARD LINK!
    newProg.writeScalaFile(ctx.settings.memo)

    newProg

  }


}
