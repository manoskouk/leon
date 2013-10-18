package leon
package memoisation

import leon._
import leon.utils._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Common._

object MemoisationPhase extends TransformationPhase {
  val name = "Memoisation transformation"
  val description = "Transform a program into another, " + 
    "where data stuctures keep memoisation information"

  implicit val debugSection = DebugSectionMemoisation

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


  def lowerCaseId (id : Identifier) = {
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
        val newId = lowerCaseId(cc.id)
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
  def makeRetreiveFun(classDef : ClassTypeDef, field : CaseClassDef) = {
    val funName = lowerCaseId(field.id)
    val retType = classDefToClassType(field)
    val args = List(new VarDecl(lowerCaseId(classDef.id), classDefToClassType(classDef)))

    val body = classDef match {
      case cc : CaseClassDef =>
        // Here the body is just retreiving the field

      case ab : AbstractClassDef =>
        // Construct the cases 
        val caseClasses = classDef.knownDescendents filter { _.isInstanceOf[CaseClassDef] }
        val patterns = caseClasses map { cc => 
          new CaseClassPatern( 
            binder       = Some(lowerCaseId(cc.id)),
            caseClassDef = cc
            // FIXME this is a dodgy way to create repeated _'s of the correct size
            subPatterns  = cc.fields map (_ => new WildcardPattern(None))
          )
        }
        val caseBodies = caseClasses map { cc =>
          

        val body = 
      }
    new FunDef

    classDef.knownDescendents 



  // FIXME: Dirty :(
  //private var ctx: LeonContext = null 

  def apply (ctx: LeonContext, p: Program) = {

    val dbg = ctx.reporter.debug(_)
    
    //this.ctx = ctx
    ctx.reporter.info("Hello memoisation!")
    // The functions which will be affected by memoisation and will not 
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
    val richDefForest = ( affectedDefsMap.keySet.toList filter {!_.hasParent} 
      map { makeRichClassTree(_, affectedDefsMap) }
    )
    // All new types 
    val richDefs = ( richDefForest flatMap { (classDef : ClassTypeDef) => classDef match {
      case ab: AbstractClassDef => ab.knownDescendents
      case cc: CaseClassDef     => List()
    }} ) ++ richDefForest
    
    /*** DEBUG ***/
    dbg("NEW TYPES")
    richDefs foreach (df => dbg(df) )
    /*** DEBUG ***/

    

    p
  }


  
  /*
   * Takes a pair of a class and a list of recursive
   * functions where this class appears as the only parameter,
   * and returns a list of definitions for a new equivalent program
   */
/*  def processTypes ( defFuns : Map[ClassTypeDef, List[FunDef]])  = {

    val dbg = ctx.reporter.debug(_)

    val (classDef, funs) = defFuns
    
    
   
    def newClasses(classDef: ClassTypeDef, fields: CaseClassDef) : Seq[ClassTypeDef]= {
      def knownLeafDescendentsInclusive(cl : ClassTypeDef) = cl match {
        case ab : AbstractClassDef => ab.knownDescendents.filter(_.isInstanceOf[CaseClassDef])
        case cc : CaseClassDef => List(cc)
      }
      val newCaseCls = knownLeafDescendentsInclusive(classDef) map ( cl => {
        new CaseClassDef(cl.id, None)
      )
      newCaseCls foreach { _.fields = fields :+ fields }

      newCaseCls

    }
    
    def makeExtraFields(classDef:ClassTypeDef) : List[ CaseClassDef ]= {
      defFuns.find(classDef).
        getOrElse(List()).
        map(fieldsConstruct)
*/

    /*
     * Take a class tree under classDef, and the new fields to be added,
     * and recursively reconstruct it with the new fields
     */
/*
    def newClassTree(classDef: ClassTypeDef, fields: CaseClassDef) : Seq[ClassTypeDef]= {
      def rec (classDef: ClassTypeDef, // current tree point
        ancestorFields: List[CaseClassDef] // fields inherited from parent
      ) = classDef match {
        cc : CaseClassDef => 
          val newcc = new CaseClassDef(cc.id)
          // Keep old fields, add the extra from this class plus given from parent
          newcc.fields = cc.fields ++ 

        ab : AbstractClassDef => 
          // Find what fields you have to add to children 
          val newFields = 
          // initialize object
          val newAb = new AbstractClassDef(ab.id)
          // recursively create children
          children = ab.knownChildren map rec
        

      def knownLeafDescendentsInclusive(cl : ClassTypeDef) = cl match {
        case ab : AbstractClassDef => ab.knownDescendents.filter(_.isInstanceOf[CaseClassDef])
        case cc : CaseClassDef => List(cc)
      }
      val newCaseCls = knownLeafDescendentsInclusive(classDef) map ( cl => {
        new CaseClassDef(cl.id, None)
      )
      newCaseCls foreach { _.fields = fields :+ fields }

      newCaseCls

    }

    dbg("Received class " + classDef)
    dbg("and funs: " + funs mkString (", "))
    val (abstrFields, concrFields) = fieldsConstruct(classDef, funs)
    dbg("New classes: " + abstrFields + concrFields)
    val newCaseCls = newCaseClasses(classDef, concrFields)
    dbg("New class definition: " + newCaseCls mkString ", ")

  }

  
 
  //def addFields(t:TypeDef
*/
}
