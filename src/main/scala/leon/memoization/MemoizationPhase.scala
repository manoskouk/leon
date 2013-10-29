package leon
package Memoization

import leon._
import leon.utils._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Common._

object MemoizationPhase extends TransformationPhase {
  val name = "Memoization transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep Memoization information"

  /*
  trait TypeDefTree[+A <: ClassTypeDef] {
  
    val p : Program
    val classDef : A
    val parent : Option[TypeDefTree[AbstractClassDef]]

    val children : List[TypeDefTree[A]]
    lazy val descendents : List[TypeDefTree[A]]= children match { 
      case Nil => Nil 
      case _   => children ++ (children flatMap { _.descendents })
    }

    lazy val caseDescendents = descendents filter { _.isLeaf }
    
    def isLeaf : Boolean = classDef match {
      case _ : CaseClassDef  => true
      case _                 => false
    }

    def hasParent = !parent.isEmpty
  }
  */

  abstract class MemoClassRecord[+A <: ClassTypeDef](
    val p : Program,
    val classDef : A,
    val parent : Option[MemoClassRecord[AbstractClassDef]] 
  )  { //extends TypeDefTree[A] {
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

    def hasParent = !parent.isEmpty
  
    // Recursively gather all results of the given function from the top of the tree
    def collectFromTop[A](fn : MemoClassRecord[_] => A ) : List[A] = parent match {
      case None       => List(fn(this))
      case Some(prnt) => fn(this) :: prnt.collectFromTop[A](fn)
    }


    // The new program resulting from this tree
    def newProgram : List[Definition] = {
      val localDefs : List[Definition] =
        richClassDef ::   
        { fieldExtractor.toList } ++ 
        { extraFieldAbstr.toList } ++ 
        { extraFieldConcr.toList } ++  
        { constructor.toList } ++
        {  memoizedFuns } ++ 
        List()
      localDefs ++ ( children flatMap { _.newProgram } )
    }
      
    // The rich type corresponding to classDef
    val richClassDef: A
    lazy val richType =  classDefToClassType(richClassDef)
    
    def hasExtraFields = !(richClassDef == classDef)


    // Functions which recursively call themselves with their only argument being of type classDef
    val classDefRecursiveFuns : List[FunDef] = p.definedFunctions.toList filter { f => 
      p.transitivelyCalls(f,f) &&
      f.args.size == 1 &&
      f.args.head.getType.asInstanceOf[ClassType].classDef == classDef
    } 


    // The fields a type has to add are all classDefRecursiveFuns of its ancestors (inclusive)
    //val funsToMemoize : List[List[FunDef]] = parent match {
    //  case Some(pr) => this.classDefRecursiveFuns :: pr.classDefRecursiveFuns
    //  case None     => List(this.classDefRecursiveFuns)
   // }
    
    val hasLocalMemoFuns = !classDefRecursiveFuns.isEmpty


    // New versions of funsToMemoize, utilizing the memoized field
    def memoizedFuns : List[FunDef] = classDefRecursiveFuns map { fn =>
      // Identifier of the input function
      val oldArg = fn.args.head.id
      // the new argument will have the new type corresponding to this type
      val newArg = new VarDecl(FreshIdentifier(oldArg.name), richType ) 
      val newFun = new FunDef(
        id = FreshIdentifier(fn.id.name),
        returnType = fn.returnType, // FIXME!!! need to search for the new type corresponding to the old one
        args = List(newArg)
      )
      // The object whose field we select is an application of fieldExtractor on newArg
      val argVar = new Variable(newArg.id)
      argVar.setType(richType)
      val bodyObject = new FunctionInvocation( fieldExtractor.get, List(argVar) )
      newFun.body = Some(CaseClassSelector(
        extraFieldConcr.get, 
        bodyObject, 
        extraFieldConcr.get.fields.find{ _.id.name == fn.id.name }.get.id
      ))

      newFun
    }

   

    val funsToRenew : List[FunDef]
    val renewedFuns : List[FunDef]

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
      val args = List(new VarDecl(paramName, richType)) // classDefToClassType(richClassDef)))

      // Body of resulting function
      val body: Expr = richClassDef match { // FIXME changed to rich
        case cc : CaseClassDef =>
          // Here the body is just retreiving the field
          CaseClassSelector(cc, new Variable(idToLowerCase(cc.id)), funName)
        case ab : AbstractClassDef => {
          // Construct the cases :
          // The case classes on which we will match
          val caseClasses : List[CaseClassDef]= ( this.caseDescendents 
            map { _.richClassDef.asInstanceOf[CaseClassDef] } 
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
              new Variable(idToLowerCase(cc.id)), // FIXME maybe needs the pattern binder
              cc.fields.find( _.id.name == funName.name ).get.id
            )
          }
          
          // complete cases
          val cases = (patterns zip caseBodies) map { case (patt, bd) => new SimpleCase(patt, bd) }

          // the variable to do case analysis on
          val scrutinee = new Variable(paramName)
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
    val funsToRenew: List[FunDef] = Nil // FIXME 
    val renewedFuns: List[FunDef] = Nil // FIXME 

    // Here some real work is done: we may have to add a field if we have any functions
    val richClassDef: CaseClassDef = {
      val allExtraFields = collectFromTop(_.extraFieldConcr).flatten.map{varFromClassDef(_)}
      if (allExtraFields.isEmpty) classDef
      else {
        val newCc = new CaseClassDef(classDef.id.freshen)
        newCc.fields = classDef.fields.toList ++ allExtraFields
        // FIXME maybe renew all fields?
        parent match {
          case Some(prnt) => newCc.setParent(prnt.richClassDef)
          case None =>
        }
        newCc
      }
    }
  
    val constructor: Option[FunDef] = { 
      if (!hasExtraFields) None 
      else { /*
        // Find all functions which define fields
        val memoFuns = collectFromTop(_.classDefRecursiveFuns).flatten
        

        // Take a function with argument a supertype of classDef and 
        // isolate the match cases concerning classDef
        def isolateMatchCase (fn : FunDef) : Expr = {
          val arg = fn.args.head

          


          def refersToType(e : Expr) 
          searchAndReplace(fn.body) 
            
        } */

        val args = classDef.fields
        Some( new FunDef(
          FreshIdentifier("create" + classDef.id.name),
          richType,
          args // FIXME!!!
        ))


        //FIXME add body
      }
    }

  }

  class MemoAbstractClassRecord (
    p : Program,
    classDef : AbstractClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]] 
  ) extends MemoClassRecord[AbstractClassDef](p,classDef,parent) {
    
    val constructor: Option[FunDef] = None
    val funsToRenew: List[FunDef] = Nil // FIXME
    val renewedFuns: List[FunDef] = Nil // FIXME 
    val richClassDef: AbstractClassDef = {
      val newAb = 
        new AbstractClassDef(classDef.id.freshen )
      parent match {
        case Some(prnt) => newAb setParent prnt.richClassDef
        case None       =>
      }
      newAb
    }
    
    // recursive! 
    val children : List[MemoClassRecord[ClassTypeDef]]= classDef.knownChildren.toList map {
      case ab : AbstractClassDef => 
        new MemoAbstractClassRecord(p, ab, Some(this))
      case cc : CaseClassDef =>
        new MemoCaseClassRecord(p, cc, Some(this))
    }

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
   * OLD STUFF
   *

  // Find which functions are affected by the transformation
  def isAffectedFunction(p : Program, f : FunDef) = {
      p.transitivelyCalls(f,f) && 
      f.args.size == 1 &&
      f.args.head.getType.isInstanceOf[ClassType]
  }

  // From type and related functions, find the relevant type declaration and make related new types
  def findClassDefAndMakeFieldConstructs(p : Program, tpFuns : (ClassType, Seq[FunDef])) = tpFuns match {
    case (tp, funs) => {
      val defin = p.definedClasses.find(_.id == tp.id).
          getOrElse(scala.sys.error("Did not find definition for type " + tp.id.toString))
      val (abst, concr) = makeFieldsConstruct(defin, funs)
      ( defin, (funs, abst, concr)  )  
    }
  }


  // Construct the new type with all the extra fields
  def makeFieldsConstruct( classDef : ClassTypeDef, funs: Seq[FunDef] ) : (AbstractClassDef, CaseClassDef) = {
   
    val abstr = new AbstractClassDef(id = FreshIdentifier(classDef.id + "FieldsAbstract"))
    
    val concr = new CaseClassDef(id = FreshIdentifier(classDef.id + "Fields") )
    concr.setParent(abstr)
    concr.fields = funs map {fn => new VarDecl(fn.id, fn.returnType) } 

    (abstr, concr)

  }


    
  *
  */

  /*
   * Take a class tree under classDef, and the new fields to be added,
   * and recursively reconstruct it with the new fields
   */


  /*
  def makeRichClassTree(classDef: ClassTypeDef,  
    affectedDefsMap : Map[ ClassTypeDef, (Seq[FunDef], AbstractClassDef, CaseClassDef ) ]
  ) : ClassTypeDef = {
    
    // current tree point, field inherited from father
     
    def rec (classDef: ClassTypeDef, ancestorFields: Seq[VarDecl] ) : ClassTypeDef = {

      // Find the concrete fields to add in the definition map
      def getNewFields(classDef : ClassTypeDef) : Option[CaseClassDef] = {
        (affectedDefsMap get classDef) map { _._3 } 
      }

      // Take a ClassTypeDef and make a field with the same name (lower-case) 
      // and the correct type
      def varFromClassDef(cc : ClassTypeDef) : VarDecl = {
        val newId = idToLowerCase(cc.id)
        new VarDecl(newId, classDefToClassType(cc) )
      }
      
      classDef match {
        case cc : CaseClassDef => 
          val newCc = new CaseClassDef(cc.id)
          // Keep old fields, add the extra from this class plus given from parent
          newCc.fields = getNewFields(cc) match {
            case None     => cc.fields ++ ancestorFields
            case Some(cl) => cc.fields ++ ( varFromClassDef(cl) +: ancestorFields )
          }
          newCc

        case ab : AbstractClassDef => 
          // initialize object
          val newAb = new AbstractClassDef(ab.id)
          // Find what fields you have to add to children and rec. create them
          val passedDownFields = getNewFields(ab) match {
            case None => ancestorFields
            case Some(cl) => varFromClassDef(cl) +: ancestorFields
          }
          val newChildren = ab.knownChildren map { ch => rec(ch, passedDownFields) }
          // Register the new object as parents of the children
          newChildren foreach { _.setParent(newAb) }
          newAb
      }
    }


    rec(classDef, List[VarDecl]())

  }
*/

/*
  // Make a function that retrieves the newly created fields from the new types
  def makeRetrieveFun(classDef : ClassTypeDef, //Tree 
    field : CaseClassDef //TreeFields
  ) = {

    // Name of the field
    //val fieldId = FreshIdentifier(classDef.id.toString ++ "Fields", 
    // Name of resulting function
    val funName = idToLowerCase(field.id) // treeFields
    // Return type of res. function
    val retType = classDefToClassType(field) // TreeFields
    // Args of resulting function
    val args = List(new VarDecl(idToLowerCase(classDef.id) , classDefToClassType(classDef) ))

    // Body of resulting function
    val body: Expr = classDef match {
      case cc : CaseClassDef =>
        // Here the body is just retreiving the field
        CaseClassSelector(cc, new Variable(idToLowerCase(cc.id)), funName)
      case ab : AbstractClassDef => {
        // Construct the cases :
        // The case classes on which we will match
        val caseClasses = ( ab.knownDescendents 
          filter { _.isInstanceOf[CaseClassDef] } 
          map { _.asInstanceOf[CaseClassDef] }
        )
        // Case patterns
        val patterns = caseClasses map { cc => 
          new CaseClassPattern( 
            binder       = Some(idToLowerCase(cc.id)),
            caseClassDef = cc,
            // FIXME this is a dodgy way to create repeated _'s of the correct size
            subPatterns  = cc.fields map (_ => new WildcardPattern(None))
          )
        }
        // case bodies
        val caseBodies = caseClasses map { cc => 
          //dbg(cc.toString)
          //dbg(funName.toString)
          new CaseClassSelector(cc, new Variable(idToLowerCase(cc.id)), cc.fields.find(_.id.name == funName.name ).get.id)
        }
        
        // complete cases
        val cases = (patterns zip caseBodies) map { case (patt, bd) => new SimpleCase(patt, bd) }

        // the variable to do case analysis on
        val scrutinee = new Variable(idToLowerCase(ab.id))
        scrutinee.setType(classDefToClassType(ab))

        // The complete match expr.
        MatchExpr(scrutinee, cases)
      }
    }

    // Now construct the whole definition and add body
    val funDef = new FunDef(funName, retType, args)
    funDef.body = Some(body)

    funDef
  }

*/
  // FIXME: Dirty :(
  //private var ctx: LeonContext = null 

  def apply (ctx: LeonContext, p: Program) = {

    def dbg(x:Any) = ctx.reporter.debug(x.toString)
    this.ctx = ctx

    //this.ctx = ctx
    ctx.reporter.info("Hello Memoization!")

    
    val testNew = true
    if (testNew) {
      val defTrees = p.classHierarchyRoots.toList map { 
        case ab : AbstractClassDef => 
          new MemoAbstractClassRecord(p, ab, None)
        case cc : CaseClassDef =>
          new MemoCaseClassRecord(p, cc, None)
      }

      //dbg ( "I have " + defTrees.length + " trees")
      val newDefs = defTrees flatMap { _.newProgram }
      newDefs map (df => dbg(df))
    }

    else {

      /* OLD STUFF

      // The functions which will be affected by Memoization and will not 
      val (affectedFuns, notAffectedFuns) = p.definedFunctions.partition(isAffectedFunction(p,_))
    
      / *** DEBUG *** /
      dbg("Affected functions:")
      affectedFuns.foreach( fn => dbg(fn.id))
      / *** DEBUG *** /
    

      val affectedTypes = affectedFuns.groupBy(_.args.head.getType.asInstanceOf[ClassType])
      //Definitions that will get affected, along with functions and new required classes
      val affectedDefsMap : Map[ ClassTypeDef, (Seq[FunDef], AbstractClassDef, CaseClassDef ) ] = 
        affectedTypes map { findClassDefAndMakeFieldConstructs(p,_) }

      / *** DEBUG *** /
      affectedDefsMap foreach { case (classDef, (funs, abstr, concr) ) => 
        dbg("Class " + classDef)
        dbg("is called by funs")
        funs foreach { fn => dbg("  " + fn.id) }
        dbg("new types to be created: " + abstr + " and " + concr)

      }
      / *** DEBUG *** /

      // Create the new type forest. Only apply to roots of the forest to not repeat yourself
      val richDefForest = ( 
        affectedDefsMap.keySet.toList 
        filter {!_.hasParent} 
        map { makeRichClassTree(_, affectedDefsMap) }
      )
      // All new types 
      val richDefs : List[ClassTypeDef]= ( richDefForest flatMap { (classDef : ClassTypeDef) => classDef match {
        case ab: AbstractClassDef => ab.knownDescendents
        case cc: CaseClassDef     => List()
      }} ) ++ richDefForest
    
      / *** DEBUG *** /

      dbg("NEW TYPES")
      richDefs foreach (df => dbg(df) )
      
      dbg("OLD TYPES")
      affectedDefsMap foreach (df => dbg(df._1))
      / *** DEBUG *** /
      

      // For the new types, recreate the map that will 
      val richDefsMap : Map[ ClassTypeDef, Option[(Seq[FunDef], AbstractClassDef, CaseClassDef )] ] = {
        (richDefs map { rich => rich -> (
          affectedDefsMap find { _._1.id == rich.id } map { _._2} 
        )}).toMap
      }
      
      
      / *** DEBUG *** /
      dbg("RICH MAP")
      richDefsMap foreach { df => dbg(df._1)  ;   dbg(df._2)    }
      / *** DEBUG *** /
      
      val retrieveFuns = richDefs map { df => 
        affectedDefsMap find { _._1.id == df.id } map { fields => makeRetrieveFun(df, fields._2._3) }  
      }
      
      / *** DEBUG *** /
      dbg("RETRIEVE FUNS")
      retrieveFuns foreach (df => dbg(df) )
      / *** DEBUG *** /

    *
    */
    }

    p
  }


}
