package Assignment3.Source
import scala.collection.immutable.ListMap
import Assignment3.Utility.Utility._
import Assignment3.SourceHelpers.SourceHelpers._
// Source language
object Source {
  type TermVariable = Variable
  type TypeVariable = Variable
  type Label = String
  type ClassName = String
  type ObjectName = String

  // - Types
  abstract class Type
  case class TyVar(x: TypeVariable) extends Type
  case object TyTop extends Type
  case class TyObject(bnd: TypeVariable, fields: ListMap[Label, Type]) extends Type
  case class TyClass(ty: Type) extends Type
  case object TyBool extends Type
  case object TyInt extends Type
  case object TyString extends Type
  case class TyFun(args: List[Type], res: Type) extends Type

  // - Expressions
  abstract class Expr
  case class Var(name: TermVariable) extends Expr

  case class Func(params: List[(Variable, Type)], body: Expr) extends Expr
  case class Apply(e: Expr, args: List[Expr]) extends Expr

  // -- Object-oriented features
  case class SelectField(obj: Expr, methodLabel: Label) extends Expr
  case class MethodUpdate(
    obj: Expr,
    methodLabel: Label,
    selfVar: Variable,
    selfTy: Type,
    newBody: Expr) extends Expr
  case class FieldUpdate(obj: Expr, fieldLabel: Label, newBody: Expr) extends Expr
  case class New(c: Expr) extends Expr

  // Root
  case object RootClass extends Expr

  // --- Type synonym
  case class TypeIn(tv: TypeVariable, ty: Type, e: Expr) extends Expr

  // --- Let binding
  case class LetIn(x: TermVariable, e1: Expr, e2: Expr) extends Expr

  // --- Object definition
  case class Object(
    selfBinder: TypeVariable,                 // Name of the self binder
    selfTy: Type,                   // Type of the object
    fields: ListMap[Label, Expr])             // Fields / Methods of the object
  extends Expr
  // --- Class definition
  case class Class(
    selfBinder: Variable,                                // Name of the self binder
    selfType: Type,                            // Type annotation on the self binder
    extendsData: Option[(Expr, Type)],     // Superclass, type
    fields: ListMap[Label, Expr],                        // Map from labels to methods, _not overridden_
    overriddenMethods: ListMap[Label, Expr]              // Map from labels to methods, where labels occur in superclass
  ) extends Expr

  // -- Basic terms
  case class IfThenElse(e1: Expr, e2: Expr, e3: Expr) extends Expr
  case class Bool(b: Boolean) extends Expr
  case class Num(n: Integer) extends Expr
  case class Str(str: String) extends Expr
  case class BinOp(op: BinaryOp, e1: Expr, e2: Expr) extends Expr
  case class NotOp(e: Expr) extends Expr


  abstract class BinaryOp
  case object EqOp extends BinaryOp
  case object AddOp extends BinaryOp
  case object SubOp extends BinaryOp
  case object MulOp extends BinaryOp
  case object DivOp extends BinaryOp
  case object AndOp extends BinaryOp
  case object OrOp extends BinaryOp

  // - Typechecking

  type TermVarEnv = ListMap[Variable, Type]


  // Typechecks a program (closed expression)
  def typecheckProgram(term: Expr): Type = {
    typeCheck(new ListMap(): TermVarEnv, term)
  }

  def typeCheck(termEnv: TermVarEnv, term: Expr): Type = {

    // Helper definitions
    /*
    * Helper definitions -- remember we have provided:
    *  - subtypeOf: (Type, Type) => Boolean
    *  - typeSwap: (Type, TypeVariable, TypeVariable) => Type
    *  - typeSubst: (Type, Type, TypeVariable) => Type
    *  - equivTypes: (Type, Type) => Boolean
    */

    // tc checks a term under the current environment
    def tc(e: Expr): Type = typeCheck(termEnv, e)

    // assertTy typechecks a term, and throws an error if it doesn't have
    // the given type.
    def assertTy(term: Expr, asserted: Type): Unit = {
      val termTy = tc(term);
      if(equivTypes(termTy, asserted)) { () } else {
        sys.error("Got type " + termTy.toString +
          ", but expected type " + asserted.toString)
      }
    }

    //for use in Func: takes parameter list and initial environment and returns list of types
    //in parameter list and an environment variable constructed by forming mappings from pairs
    //in parameter list
    def FuncHelper(params: List[(Variable, Type)]): (List[Type], TermVarEnv) = params match{
    	case Nil => (List(), ListMap.empty[Variable, Type])
	case (v, ty) :: xs => {
	     val (a, b) = FuncHelper(xs)
	     (ty :: a, b + (v -> ty))
	}
	     
	
    }

    term match {
    	 case TypeIn(_, _, _) => sys.error("INTERNAL ERROR! TypeIn SHOULD NOT APPEAR. Please report this!")

	 case Object(selfBinder, selfTy, fields) => selfTy match {
	      case TyObject(bind, typeFields) => {
	      	   for ((tyLabel, expType) <- typeFields) {
		       val e = fields.apply(tyLabel)
		       if (!(equivTypes(typeCheck(termEnv + (selfBinder -> selfTy), e), expType))){
		       	  sys.error("fields in object do not have equivalent types as in expected TyObject")
		       }
		   }
		   if (fields.size > typeFields.size) sys.error("extra fields found in object vs. its type")
		   selfTy
	      }
	      case _ => sys.error("object must be of a valid TyObject")
	 }

	 case SelectField(obj, methodLabel) => {
	      val objType = tc(obj) match {
	      	  case TyObject(bnd, typeFields) => TyObject(bnd, typeFields)
		  case _ => sys.error("field access must be performed on a valid object")
	      }
	      val expType = objType.fields.apply(methodLabel)
	      typeSubst(expType, objType, objType.bnd)
	 }
	

	 case FieldUpdate(obj, fieldLabel, newBody) => tc(obj) match {
	      case TyObject(bind, fields) => {
	      	   val expType = fields.apply(fieldLabel)
		   //so for some reason I need to specify return here? simply putting tc(obj) does nothing
		   //and results in going to the error in test running, even though the statement is true
		   if (equivTypes(tc(newBody), typeSubst(expType,TyObject(bind,fields),bind))){return tc(obj)}
		   sys.error("updated version of method does not have same type as previous")
	      }
	      case _ => sys.error("field update must be performed on a valid object")

	 }
	 case MethodUpdate(obj, methodLabel, selfVar, selfTy, newBody) => tc(obj) match {
	      case TyObject(bind, fields) => {
	      	   val expType = fields.apply(methodLabel)
		   if (!equivTypes(tc(obj),selfTy)) {sys.error("self variable of method must have same type as object")}
		   if (equivTypes(typeCheck(termEnv + (selfVar -> selfTy),newBody), typeSubst(expType, selfTy, bind))){return selfTy}
		   sys.error("updated version of method does not have same type as previous")
	      }
	 }

	 case New(e) => tc(e) match {
	      case TyClass(ty) => ty match {
	      	   case TyObject(_,_) => ty
		   case _ => sys.error("class must contain a valid object type")
	      }
	      case _ => sys.error("e muse have a type TyClass")

	 }
	 
	 case RootClass => TyClass(TyObject("X", ListMap.empty[Label, Type]))

	 case Class(selfBinder, selfType, extendsData, fields, overridenMethods) => extendsData match{

	      case Some((expr, ty)) => {
	      	   val (selfObj, objFields) = selfType match {
	      	       	case TyObject(f1, f2) => (f1, f2)
		   	case _ => sys.error("class must contain a valid object type")
	      	   }
	      	   val superTyObj = tc(expr) match{
		       case TyClass(f1) => f1
		       case _ => sys.error("type being extended must be a valid class")
		   }
		   val (superTyObjbnd, superTyObjfields) = superTyObj match {
		       case TyObject(f1, f2) => (f1, f2)
		       case _ => sys.error("can't believe this got to this point")
	 	   }
		   if (subtypeOf(selfType, superTyObj)) {
		       //separate fields of the TyObject between overriden and non-overriden
		       //to ensure all needed fields are checked in the declared Object
		       for ((objFieldsLabel, objFieldsType) <- objFields) {
		       	   if (!(overridenMethods.contains(objFieldsLabel))&&
			   !(superTyObjfields.contains(objFieldsLabel))) {
			      fields.get(objFieldsLabel) match {
				case None => sys.error("improper class declaration; missing field")
				case _  => {
				     if (!(equivTypes(tc(fields.apply(objFieldsLabel)),objFieldsType))) {
				     	sys.error("a field in class does not match type of field in contained TyObject")
					}
				}
			      }
		    	   }
			}
			for ((fieldsLabel, _) <- fields) {
			    if (!objFields.contains(fieldsLabel)) {
			       sys.error("extra field declared in class beyond those included in object type")
			    }
			    if (superTyObjfields.contains(fieldsLabel)) {
			       sys.error("attempted to overwrite field from superclass that was not included in map of overriden fields")
			    }
			}
			for ((superObjLabel, superObjType) <- superTyObjfields) {
			    objFields.get(superObjLabel) match {
			    	    case None => sys.error("missing inherited field")
				    case _ => {
				    	 if (!(equivTypes(typeSubst(objFields.apply(superObjLabel),
											selfType,selfObj),
							typeSubst(superObjType,superTyObj,superTyObjbnd))))
					 {
						sys.error("fields in extending class object inherited from super class must match type to those in the super class object")
					 }
				     }
			     }
			 }
			 for ((overridenLabel, overridenExpr) <- overridenMethods) {
			     objFields.get(overridenLabel) match {
		      		case None => sys.error("class declaration has an extra overriden method declared")
		          	case _ => {
		       		     if (!(equivTypes(typeCheck(termEnv + (selfBinder -> selfType), overridenExpr), objFields.apply(overridenLabel)))) {
			       	  	     sys.error("overriden method has invalid type vs Object definition")
		      	  	     }
				}
			     }
			 }
			 TyClass(selfType)
		    }		
		   else {
		   	sys.error("object type must be a valid subtype of the object type in the super class")
		   }
	      }

	      case None => {
	      	   val rootty = tc(RootClass)
	      	   tc(Class(selfBinder,selfType,Some(RootClass,rootty), fields, overridenMethods))
	      }
	 }

	 case Var(v) => termEnv(v)

	 case Func(params, body) => {
	      val (typeList, extraEnv) = FuncHelper(params)
	      TyFun(typeList, typeCheck(termEnv ++ extraEnv, body))
	 }

	 case Apply(e, args) => tc(e) match{
	      case TyFun(typeList, bodyType) => {
	      	   //compare each argument i in funTypes to each argument j in argList to ensure
		   //j <: i, else function call is invalid
	      	   def ApplyHelper(funTypes:List[Type], argList: List[Expr]): Type = (funTypes, argList) match {
		       case (Nil, Nil) => bodyType
		       
		       case (funTy :: funs, argx :: argxs) => {
		       	    if (subtypeOf(tc(argx), funTy)) {
			       ApplyHelper(funs,argxs)
			    }
			    else{
				sys.error("an argument is not a valid subtype of its matching parameter")
			    }
		       }
		       case _ => sys.error("Invalid function application, perhaps missing arguments")
		   }
		   ApplyHelper(typeList,args)
	      }
	      case _ => sys.error("Function application must be performed using a valid function")
	 }

	 case LetIn(x, e1, e2) => typeCheck(termEnv + (x -> (tc(e1))), e2)

	 case IfThenElse(e1, e2, e3) => (tc(e1),tc(e2),tc(e3)) match {
	      case (TyBool, a, b) => if (equivTypes(a,b)) {
	      	   a
	      }
	      else{
		sys.error("types of branches must be equal")
	      }
	      case (_,a,b) => sys.error("type of conditional must be boolean")
	 }
	 case Bool(v) => TyBool
	 case Num(v) => TyInt
	 case Str(v) => TyString

	 case BinOp(op, e1, e2) => op match {
	      case EqOp => (tc(e1),tc(e2)) match {
	      	   case (a, b) => if (equivTypes(a,b)) {
		   	a match {
			  case TyInt => TyBool
			  case TyBool => TyBool
			  case TyString => TyBool
			  case _ => sys.error("types must be simple")
			}
		   	
		   }
		   else{
			sys.error("types to be compared for equality must be identical")
		   }
	      }
	      case AndOp => (tc(e1),tc(e2)) match {
	      	   case (TyBool, TyBool) => TyBool
		   case (_,_) => sys.error("types of and operation must be boolean")
	      }
	      case OrOp => (tc(e1),tc(e2)) match {
	      	   case (TyBool, TyBool) => TyBool
		   case (_,_) => sys.error("types of or operation must be boolean")
	      }
	      case _ => (tc(e1),tc(e2)) match {
	      	   case (TyInt,TyInt) => TyInt
		   case (_,_) => sys.error("types of arithmetic operation must be int")
	      }
	 }

	 case NotOp(e) => tc(e) match {
	      case TyBool => TyBool
	      case _ => sys.error("type in not operation must be boolean")
	 }
	 case _ => sys.error("TODO -- fill me in!")
    }
  }
}



// vim: set ts=2 sw=2 et sts=2:
