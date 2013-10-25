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
      case _ :CaseClassDef  => true
      case _                => false
    }

    def hasParent = !parent.isEmpty
  }

  abstract class MemoClassRecord[+A <: ClassTypeDef] extends TypeDefTree[A] {
  /*
    // Recursive!
    lazy val children : List[MemoRecord] = classDef match {
      case ac : AbstractClassDef => 
        ac.knownChildren.toList map { new MemoRecord(_, Some(this), p) }
      case cc : CaseClassDef =>
        Nil
    }
  */ 
    // The rich type corresponding to classDef
    val richType: A

    // Functions which recursively call themselves with their only argument being of type classDef
    val classDefRecursiveFuns : List[FunDef] = p.definedFunctions.toList filter { f => 
      p.transitivelyCalls(f,f) &&
      f.args.size == 1 &&
      f.args.head.getType.asInstanceOf[ClassType].classDef == classDef
    } 

    // The fields a type has to add are all classDefRecursiveFuns of its ancestors (inclusive)
    val funsToMemoize = parent match {
      case Some(pr) => this.classDefRecursiveFuns ++ pr.classDefRecursiveFuns
      case None     => this.classDefRecursiveFuns
    }

    // New versions of funsToMemoize, utilizing the memoized field
    def memoizedFuns  : List[FunDef]  = funsToMemoize map { fn =>
      // Identifier of the input function
      val fnId = fn.args.head.id
      // the new argument will have the new type corresponding to this type
      val newArg = new VarDecl(fn.args.head.id.freshen, classDefToClassType(richType))
      val newFun = new FunDef(
        id = FreshIdentifier(fn.id.name),
        returnType = null, // FIXME!!! need to search for the new type corresponding to the old one
        args = List(newArg)
      )
      // The object whose field we select is an application of fieldExtractor on newArg
      val bodyObject = new FunctionInvocation( fieldExtractor, List(new Variable(newArg.id)) )
      newFun.body = Some(CaseClassSelector(
        extraFieldConcr, 
        bodyObject, 
        extraFieldConcr.fields.find{ _.id.name == fnId.name }.get.id
      ))

      newFun
    }

    val funsToRenew : List[FunDef]
    val renewedFuns : List[FunDef]

    // Extra fields we are adding to the type
    lazy val extraFieldAbstr = 
      new AbstractClassDef(id = FreshIdentifier(classDef.id + "FieldsAbstract"))
    lazy val extraFieldConcr = {
      val concr = new CaseClassDef(id = FreshIdentifier(classDef.id + "Fields") )
      concr.setParent(extraFieldAbstr)
      concr.fields = funsToMemoize map { fn => new VarDecl(fn.id.freshen, fn.returnType) } 
      concr
    }


    val constructor: FunDef

    

    // Make a function that retrieves the newly created fields from the new types
    // This function has to separate cases for the leaf types of this type
    def fieldExtractor : FunDef = {
      
      // Running example in the comments : say we start with a class called ClassName 

      // Name of resulting function e.g. classNameFields
      val funName = idToLowerCase(extraFieldConcr.id) 
      // Return type of res. function. e.g. ClassNameFields
      val retType = classDefToClassType(extraFieldConcr) 
      // Name of parameter e.g. className
      val paramName = idToLowerCase(classDef.id)
      // Args of resulting function, e.g. ( className : ClassName )
      val args = List(new VarDecl(paramName, classDefToClassType(classDef)))

      // Body of resulting function
      val body: Expr = classDef match {
        case cc : CaseClassDef =>
          // Here the body is just retreiving the field
          CaseClassSelector(cc, new Variable(idToLowerCase(cc.id)), funName)
        case ab : AbstractClassDef => {
          // Construct the cases :
          // The case classes on which we will match
          val caseClasses : List[CaseClassDef]= ( this.caseDescendents 
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
            dbg(cc.toString)
            dbg(funName.toString)
            new CaseClassSelector(cc, new Variable(idToLowerCase(cc.id)), cc.fields.find(_.id.name == funName.name ).get.id)
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

      funDef
    }


  }
/*
  class MemoCaseRecord (
    classDef : CaseClassDef, 
    parent : Option[MemoClassRecord[AbstractClassDef]], 
    p : Program
  ) extends MemoClassRecord[CaseClassDef] {
    
    val children = Nil

    val affectedFuns: List[leon.purescala.Definitions.FunDef] = ???
    val constructor: leon.purescala.Definitions.FunDef = ???
    val fieldExtractor: leon.purescala.Definitions.FunDef = ???
    val memoFuns: List[leon.purescala.Definitions.FunDef] = ???
    val newField: (leon.purescala.Definitions.AbstractClassDef, leon.purescala.Definitions.CaseClassDef) = ???
    val oldAffectedFuns: List[leon.purescala.Definitions.FunDef] = ???
    val oldMemoFuns: List[leon.purescala.Definitions.FunDef] = ???



  }
*/

  implicit val debugSection = DebugSectionMemoization

  var ctx : LeonContext = null
  def dbg(x:String) = ctx.reporter.debug(x)


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


  def idToLowerCase (id : Identifier) = {
    val nm = id.name
    FreshIdentifier(nm.updated(0,nm.head.toLower))
  }

  /*
   * Take a class tree under classDef, and the new fields to be added,
   * and recursively reconstruct it with the new fields
   */

  def makeRichClassTree(classDef: ClassTypeDef,  
    affectedDefsMap : Map[ ClassTypeDef, (Seq[FunDef], AbstractClassDef, CaseClassDef ) ]
  ) : ClassTypeDef = {
    /*
     * current tree point, field inherited from father
     */
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


  // Make a function that retrieves the newly created fields from the new types
  def makeRetrieveFun(classDef : ClassTypeDef, /*Tree*/ field : CaseClassDef /*TreeFields*/ ) = {

    // Name of the field
    //val fieldId = FreshIdentifier(classDef.id.toString ++ "Fields", 
    // Name of resulting function
    val funName = idToLowerCase(field.id) // treeFields
    // Return type of res. function
    val retType = classDefToClassType(field) // TreeFields
    // Args of resulting function
    val args = List(new VarDecl(idToLowerCase(classDef.id) /* tree */, classDefToClassType(classDef) /*Tree */ ))

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
          dbg(cc.toString)
          dbg(funName.toString)
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


  // FIXME: Dirty :(
  //private var ctx: LeonContext = null 

  def apply (ctx: LeonContext, p: Program) = {

    val dbg = ctx.reporter.debug(_)
    this.ctx = ctx

    //this.ctx = ctx
    ctx.reporter.info("Hello Memoization!")
    // The functions which will be affected by Memoization and will not 
    val (affectedFuns, notAffectedFuns) = p.definedFunctions.partition(isAffectedFunction(p,_))
    
    /*** DEBUG ***/
    dbg("Affected functions:")
    affectedFuns.foreach( fn => dbg(fn.id))
    /*** DEBUG ***/
    
    
    val affectedTypes = affectedFuns.groupBy(_.args.head.getType.asInstanceOf[ClassType])
    //Definitions that will get affected, along with functions and new required classes
    val affectedDefsMap : Map[ ClassTypeDef, (Seq[FunDef], AbstractClassDef, CaseClassDef ) ] = 
      affectedTypes map { findClassDefAndMakeFieldConstructs(p,_) }

    /*** DEBUG ***/
    affectedDefsMap foreach { case (classDef, (funs, abstr, concr) ) => 
      dbg("Class " + classDef)
      dbg("is called by funs")
      funs foreach { fn => dbg("  " + fn.id) }
      dbg("new types to be created: " + abstr + " and " + concr)

    }
    /*** DEBUG ***/

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
    
    /*** DEBUG ***/
    dbg("NEW TYPES")
    richDefs foreach (df => dbg(df) )
    
    dbg("OLD TYPES")
    affectedDefsMap foreach (df => dbg(df._1))
    /*** DEBUG ***/
    

    // For the new types, recreate the map that will 
    val richDefsMap : Map[ ClassTypeDef, Option[(Seq[FunDef], AbstractClassDef, CaseClassDef )] ] = {
      (richDefs map { rich => rich -> (
        affectedDefsMap find { _._1.id == rich.id } map { _._2} 
      )}).toMap
    }
    
    
    /*** DEBUG ***/
    dbg("RICH MAP")
    richDefsMap foreach { df => dbg(df._1)  ;   dbg(df._2)    }
    /*** DEBUG ***/
    
    val retrieveFuns = richDefs map { df => 
      affectedDefsMap find { _._1.id == df.id } map { fields => makeRetrieveFun(df, fields._2._3) }  
    }
    
    /*** DEBUG ***/
    dbg("RETRIEVE FUNS")
    retrieveFuns foreach (df => dbg(df) )
    /*** DEBUG ***/



    p
  }


}
