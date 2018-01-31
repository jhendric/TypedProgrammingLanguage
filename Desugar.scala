package Assignment3.Desugar
import scala.collection.immutable.ListMap
import Assignment3.Source._
import Assignment3.Core._
import Assignment3.Utility.Utility._

// Desugaring
object Desugar {
  import Source._

  def toCoreOp(op: BinaryOp): Core.BinaryOp = op match {
    case AddOp => Core.AddOp
    case MulOp => Core.MulOp
    case SubOp => Core.SubOp
    case DivOp => Core.DivOp
    case AndOp => Core.AndOp
    case OrOp => Core.OrOp
    case EqOp => Core.EqOp
  }

  def desugar(e: Expr): Core.Expr = e match {
  
    case Class(selfBnd, selfTy, extendsData, methods, overridden) => {
        // Here, we suggest a skeleton implementation. Feel free to rewrite
        // this with your own, if you like!

        val (superclass, superty) = extendsData match {
          case Some((expr, ty)) => (expr, ty)
          case None => (RootClass, TyClass(TyObject("X", ListMap())))
        }

        val superFields = superty match {
          case TyClass(TyObject(_, fields)) => fields
          case _ =>
            sys.error("Error: supertype isn't an object. This shouldn't happen with well-typed programs.")
        }

        def getInheritedLabels(): Set[Label] = {
          sys.error("TODO: Fill me in!")
        }

        def generateNewMethod(): Core.Method = {
          sys.error("TODO: Fill me in!")
        }

        // Generate fields for inherited (non-defined) methods
        def generateInheritedMethods(inheritedLabels: Set[Label]): ListMap[Core.Label, Core.Method] = {
          sys.error("TODO: Fill me in!")
        }

        def generateDeclaredMethods(): ListMap[Core.Label, Core.Method] = {
          sys.error("TODO: Fill me in!")
        }

        def generateOverriddenMethods(): ListMap[Core.Label, Core.Method] = {
          sys.error("TODO: Fill me in!")
        }


        // Calculate the set of inherited labels (i.e. those which appear in the
        // superclass type, but are not defined or overridden)
        val inheritedLabels = getInheritedLabels()

        // Generate the "new" method
        val newMethod = generateNewMethod()

        // Generate the inherited methods
        val inheritedMethods = generateInheritedMethods(inheritedLabels)

        // Generate the declared methods
        val declaredMethods = generateDeclaredMethods()

        // Generate the overridden methods
        val overriddenMethods = generateOverriddenMethods()

        // Fields = new method + inherited methods + overridden methods
        val fields = ListMap("new" -> newMethod) ++ inheritedMethods ++ declaredMethods ++ overriddenMethods
        Core.Object(fields)
    }

    case Var(v) => Core.Var(v)

    case Object(selfBinder, selfTy, fields) => {
	 val newFields: ListMap[Core.Label, Core.Method] = for ((labelFields, exprFields) <- fields) yield (labelFields -> Core.Method(selfBinder, desugar(exprFields)))
	 Core.Object(newFields)
    }
    
    case FieldUpdate(obj, fieldLabel, newBody) => {
    	 val self = Gensym.gensym("self")
	 Core.Update(desugar(obj), fieldLabel, Core.Method(self,desugar(newBody)))
    } 

    case MethodUpdate(obj, methodLabel, selfVar, selfTy, newBody) => {
    	 Core.Update(desugar(obj), methodLabel, Core.Method(selfVar, desugar(newBody)))
    }

    case SelectField(obj, methodLabel) => {
    	 Core.Invoke(desugar(obj), methodLabel)
    }
    
    case RootClass => {
    	 Core.Object(ListMap("new" -> Core.Method("x", Core.Object(ListMap.empty[Core.Label, Core.Method]))))
    }

    case New(c) => {
    	 Core.Invoke(desugar(c), "new")
    }

    case Class(selfBinder, selfType, extendsData, fields, overridenMethods) => {
    	 sys.error("TO_DO: Class desugaring")
    }

    case Func(params, body) => {
    	 //takes params and body and recursively creates a sequence of one argument lamba abstractions
    	 def FuncHelper(paramsList: List[(Variable, Type)], body: Expr): Core.Expr = paramsList match {
	     case Nil => sys.error("no arguments to lambda expression, undiscussed case")
	     case x :: Nil => Core.Lambda(x._1, desugar(body))
	     case x :: xs => Core.Lambda(x._1, FuncHelper(xs, body))
	 }
	 FuncHelper(params, body)
    	 
    }

    case Apply(expr, args) => {
    	 //takes expr and args and recursively creates a sequence of one argument function applications
	 def ApplyHelper(expr: Core.Expr, argsList: List[Expr]): Core.Expr = argsList match {
	     case Nil => sys.error("no arguments to function application, undiscussed case")
	     case x :: Nil => Core.Apply(expr,desugar(x))
	     case x :: xs => ApplyHelper(Core.Apply(expr, desugar(x)), xs)
	 }
	 ApplyHelper(desugar(expr),args)
    }

    case LetIn(x, e1, e2) => Core.LetIn(x, desugar(e1), desugar(e2))

    case IfThenElse(e1, e2, e3) =>
      Core.IfThenElse(desugar(e1), desugar(e2), desugar(e3))

    case Bool(v) => Core.BoolV(v)

    case Num(n) => Core.NumV(n)
    
    case Str(v) => Core.StrV(v)

    case BinOp(op, e1, e2) => Core.BinOp(toCoreOp(op), desugar(e1), desugar(e2))

    case NotOp(expr) => Core.NotOp(desugar(expr))

    case _ => sys.error("TODO: Fill me in!")
  }
}

// vim: set ts=2 sw=2 et sts=2:
