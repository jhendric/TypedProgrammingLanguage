package Assignment3.Core
import scala.collection.immutable.ListMap
import Assignment3.Utility.Utility._

// Core object calculus
object Core {

  //// Definition
  type Variable = String
  type Label = String
  case class Method(selfBinder: Variable, body: Expr)

  abstract class Expr
  case class Var(name: Variable) extends Expr
  case class Object(methods: ListMap[Label, Method]) extends Expr
  case class Lambda(x: Variable, body: Expr) extends Expr
  case class Apply(f: Expr, arg: Expr) extends Expr
  case class LetIn(v: Variable, e1: Expr, e2: Expr) extends Expr
  case class Invoke(obj: Expr, methodLabel: Label) extends Expr
  case class Update(obj: Expr, methodLabel: Label, newMethod: Method) extends Expr


  // -- Basic terms
  case class IfThenElse(e1: Expr, e2: Expr, e3: Expr) extends Expr
  case class BinOp(op: BinaryOp, e1: Expr, e2: Expr) extends Expr
  case class NotOp(e: Expr) extends Expr


  abstract class BinaryOp
  case object AddOp extends BinaryOp
  case object SubOp extends BinaryOp
  case object MulOp extends BinaryOp
  case object DivOp extends BinaryOp
  case object AndOp extends BinaryOp
  case object OrOp extends BinaryOp
  case object EqOp extends BinaryOp

  abstract class Value extends Expr
  case class ObjectV(methods: ListMap[Variable, Method]) extends Value
  case class LambdaV(x: Variable, body: Expr) extends Value
  case class NumV(n: Integer) extends Value
  case class BoolV(b: Boolean) extends Value
  case class StrV(s: String) extends Value
  //// Evaluation

  // Swapping and substitution


  def swap(e: Expr, y: Variable, z: Variable): Expr = {

    def swapMethod(m: Method): Method = m match {
      case Method(x, body) =>
        Method(swapVar(x, y, z), swap(body, y, z))
    }

    def go(e: Expr): Expr = e match {
      case v: Value => v // Values are closed.
      case Var(x) => Var(swapVar(x, y, z))
      case Object(methods) => {
        val updatedMethods: ListMap[Label, Method] = methods.map((entry: (Label, Method)) => {
            val (label, body) = entry;
            (label, swapMethod(body))
        })
        Object(updatedMethods)
      }
      
      case Invoke(obj, methodLabel) => Invoke(go(obj), methodLabel)
      case Update(obj, methodLabel, method) => {
        Update(go(obj), methodLabel, swapMethod(method))
      }
      case Lambda(x, e) => {
        Lambda(swapVar(x, y, z), go(e))
      }
      case Apply(e1, e2) => Apply(go(e1), go(e2))
      case LetIn(x, e1, e2) => LetIn(swapVar(x, y, z), go(e1), go(e2))
      case IfThenElse(e1, e2, e3) => IfThenElse(go(e1), go(e2), go(e3))
      case BinOp(op, e1, e2) => BinOp(op, go(e1), go(e2))
      case NotOp(e) => NotOp(go(e))
      case e => e
    }

    go(e)
  }

  //I created this in an attempt to better swapping of self binders in methods
  def swapMethodExternal(m: Method, y: Variable, z: Variable): Method = m match{
      case Method(x, body) => Method(swapVar(x,y,z), swap(body,y,z))
  }
  
  def subst(e1: Expr, e2: Expr, x: Variable): Expr = {
    def go(e: Expr): Expr = {

      e match {
        // Values are closed -- substitution has no effect
        case v: Value => v
	case Var(y) => {
	    if (x == y) {
	       e2
	    }
	    else {
	       Var(y)
	    }
	}

	case Object(methods) => {
	     val z = Gensym.gensym("self")
	     val y = methods.head._1
	     val swappedmethods: ListMap[Label, Method] =
	     	 for ((origLabel, origMethod) <- methods) yield {
		    (origLabel, swapMethodExternal(origMethod, origMethod.selfBinder, z))
	     	 }
	     val updatedMethods: ListMap[Label, Method] =
	     	 for ((label, method) <- swappedmethods) yield {
		     (label, Method(method.selfBinder, subst(method.body, e2, x)))
		 }
	     Object(updatedMethods)
	}
	
	case Invoke(obj, methodLabel) => Invoke(go(obj), methodLabel)
	case Update(obj, methodLabel, method) => method match {
	     case Method(y, body) => {
	     	  val z = Gensym.gensym(y)
	     	  Update(go(obj), methodLabel, Method(swapVar(y, y, z), go(swap(body,y,z))))
	     }
	}
	case Lambda(y, t1) => {
             val z = Gensym.gensym(y)
             Lambda(z,subst(swap(t1,y,z),e2,x))
      	}
	case Apply(t1, t2) => Apply(go(t1),go(t2))
	case LetIn(y, t1, t2) => {
	     val z = Gensym.gensym(y)
	     LetIn(z, go(t1), subst(swap(t2,y,z),e2,x))
	}
	case IfThenElse(t1,t2,t3) => IfThenElse(go(t1),go(t2),go(t3))
	case BinOp(op, t1, t2) => BinOp(op, go(t1), go(t2))
	case NotOp(e) => NotOp(go(e))
        case _ => sys.error("TODO -- fill me in!")
      }
    }
    
    go(e1)
  }

  // Evaluation of the core calculus
  def eval(expr: Expr): Value = expr match {
    case v: Value => v
    case Var(_) => sys.error("Cannot evaluate a variable -- this should have been substituted!")
    case Object(methods) => ObjectV(methods)
    
    case Invoke(obj, methodLabel) => {
    	 eval(obj) match {
    	     case ObjectV(x) => x(methodLabel) match {
	      	  case Method(vari, body) => eval(subst(body, eval(obj), vari))
	      	  case _ => sys.error("called a nonexistent method")
	 	  }
	     case _ => sys.error("Invoke must be called on a valid Object")
    	 }
	}
    
    case Update(obj, methodLabel, method) => eval(obj) match {
		 case ObjectV(methods) => {
		    ObjectV(methods + (methodLabel -> method))		      
		 }
		 case _ => sys.error("must update on a valid object")
    }
    
    
    case Lambda(x, e) => LambdaV(x, e)
    
    case Apply(e1, e2) => {
    	 eval(e1) match {
	 	  case LambdaV(x, body) => eval(subst(body, eval(e2), x))
		  case _ => sys.error("first argument of apply must evaluate to a lambda abstraction")
	 }
    }
    
    case LetIn(x, e1, e2) => eval(subst(e2,eval(e1), x))
    
    case IfThenElse(e1, e2, e3) => {
    	 eval(e1) match {
	 	 case BoolV(true) => eval(e2)
		 case BoolV(false) => eval(e3)
		 case _ => sys.error("conditional must evaluate to a boolean")
	 }
    }
    
    case BinOp(op, e1, e2) => op match {
	    case AddOp => (eval(e1),eval(e2)) match {
	    	 case (NumV(v1), NumV(v2)) => NumV(v1+v2)
		 case _ => sys.error("arguments to addition are non-numeric")
	    }
	    case SubOp => (eval(e1),eval(e2)) match {
	    	 case (NumV(v1), NumV(v2)) => NumV(v1-v2)
		 case _ => sys.error("arguments to subtraction are non-numeric")
	    }
	    case MulOp => (eval(e1),eval(e2)) match {
	    	 case (NumV(v1), NumV(v2)) => NumV(v1*v2)
		 case _ => sys.error("arguments to multiplication are non-numeric")
	    }
	    case DivOp => (eval(e1),eval(e2)) match {
	    	 case (NumV(v1), NumV(v2)) => NumV(v1/v2)
		 case _ => sys.error("arguments to division are non-numeric")
	    }
	    case AndOp => (eval(e1),eval(e2)) match {
	    	 case (BoolV(v1), BoolV(v2)) => BoolV(v1&&v2)
		 case _ => sys.error("arguments to and statement are non-boolean")
	    }
	    case OrOp => (eval(e1),eval(e2)) match {
	    	 case (BoolV(v1), BoolV(v2)) => BoolV(v1||v2)
		 case _ => sys.error("arguments to or statement are non-boolean")
	    }
	    case EqOp => (eval(e1),eval(e2)) match {
	    	 case (BoolV(v1), BoolV(v2)) => BoolV(v1==v2)
		 case (NumV(v1), NumV(v2)) => BoolV(v1==v2)
		 case (StrV(v1), StrV(v2)) => BoolV(v1==v2)
		 case _ => sys.error("arguments to equality statement must have same type")
	    }
    }
    case NotOp(e) => {
    	 eval(e) match {
	   case BoolV(true) => BoolV(false)
	   case BoolV(false) => BoolV(true)
	   case _ => sys.error("expression must evaluate to a boolean")
	 }
    }
    case _ => sys.error("TODO -- fill me in!")
  }
}

// vim: set ts=2 sw=2 et sts=2:
