package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Hao Yuan>
   * 
   * Partner: <None>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch {case _: Throwable => Double.NaN}
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case S("") => false
      case S(_) => true
      case N(0) => false
      case N(n) => if(!n.isNaN) true else false
      case Undefined => false
      case Function(_, _, _) => true
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case N(n) => n.toString
      case B(b) => b.toString
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(x),S(y))=> bop match{
        case Lt => x < y
        case Le => x <= y
        case Gt => x > y
        case Ge => x >= y
        case _ => throw new UnsupportedOperationException
      }
      case _ => bop match{
        case Lt => toNumber(v1) < toNumber(v2)
        case Le => toNumber(v1) <= toNumber(v2)
        case Gt => toNumber(v1) > toNumber(v2)
        case Ge => toNumber(v1) >= toNumber(v2)
        case _ => throw new UnsupportedOperationException
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {

    def EV(e: Expr): Expr = eval(env, e)

    e match {

      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env,x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case Unary(uop, e1) => uop match {
        case Neg => N(-1*toNumber(EV(e1)))
        case Not => B(!toBoolean(EV(e1)))
      }

      case If(e1,e2,e3) => if(toBoolean(EV(e1))) EV(e2) else EV(e3)

      case Binary(Plus, e1, e2) => (EV(e1), EV(e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(bop @(Minus|Times|Div),e1,e2) => bop match{
        case Minus => N(toNumber(EV(e1)) - toNumber(EV(e2)))
        case Times => N(toNumber(EV(e1)) * toNumber(EV(e2)))
        case Div => N(toNumber(EV(e1)) / toNumber(EV(e2)))
      }

      case Binary(Eq, e1, e2) => (EV(e1),EV(e2)) match {
          case (Function(_,_,_),_) => throw DynamicTypeError(e)
          case (_, Function(_,_,_)) => throw DynamicTypeError(e)
          case (v1, v2) => B(EV(v1) == EV(v2))

      }
      case Binary(Ne, e1, e2) => (EV(e1),EV(e2)) match {
          case (Function(_, _, _), _) => throw DynamicTypeError(e)
          case (_, Function(_, _, _)) => throw DynamicTypeError(e)
          case (v1, v2) => B(EV(v1) != EV(v2))
        }
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, EV(e1), EV(e2)))

      case Binary(And, e1, e2) => if (toBoolean(EV(e1))) EV(e2) else EV(e1)

      case Binary(Or, e1, e2) => if (toBoolean(EV(e1))) EV(e1) else EV(e2)

      case Binary(And, v1, e2) if isValue(v1) => if(toBoolean(v1)) e2 else v1

      case Binary(Or, v1, e2) if isValue(v1) => if(!toBoolean(v1)) e2 else v1

      case Binary(Seq, e1, e2) => EV(e1); EV(e2)


      case ConstDecl(x, e1, e2) => {
        val v1 = EV(e1)
        val envp= extend(env,x,v1)
        val v2 = eval(envp,e2)
        v2
      }

      case Call(e1,e2) =>{
        val v1 =EV(e1)
        val v2 =EV(e2)
        (v1,v2) match {

          case (Function(None, x, e),ee) => eval(extend(env,x,EV(ee)),e)

          case (Function(Some(f),x,code),cc) => {

            val envp = extend(env, x, cc)
            eval(extend(envp,f,Function(Some(f),x,code)),code)

          }
          case _ =>throw DynamicTypeError(e)
        }
      }

      case _ => throw DynamicTypeError(e)
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match {
      case None => e
      case Some(ep) => loop(ep,n+1)
    }
    loop(e0, 0)
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))

    def subez(e:Expr): Expr = substitute(e, v, x) // make recall easier

    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subez(e1))

      case Unary(uop, e1) => Unary(uop,subez(e1))

      case Binary(bop, e1, e2) => Binary(bop,subez(e1),subez(e2))

      case If(e1, e2, e3) => If(subez(e1),subez(e2),subez(e3))

      case Call(e1, e2) => Call(subez(e1),subez(e2))

      case Var(y) => if(y == x) v else Var(y)

      case Function(None, y, e1) => {
        if(y == x) e else Function(None,y,subez(e1))
      }

      case Function(Some(y1), y2, e1) => {
        if(y1 == x)
          e
        else
          if(y2 == x)
            e
          else
            Function(Some(y1),y2,subez(e1))
      }

      case ConstDecl(y, e1, e2) => {
        if(y == x)
          ConstDecl(y, subez(e1), e2)
        else
          ConstDecl(y, subez(e1), subez(e2))
      }
      case _ => throw new UnsupportedOperationException
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      case Unary(uop,v1) if isValue(v1) => uop match{
        case Neg => N(-toNumber(v1))
        case Not => B(!toBoolean(v1))
      }

      case Binary(Seq, v1, e2) if isValue(v1) => e2

      case Binary(Plus, v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match {

        case(S(s), _) => S(s + toStr(v2))
        case(_, S(s)) => S(toStr(v1) + s)
        case(_, _) => N(toNumber(v1) + toNumber(v2))

      }
      case Binary(bop @ (Minus|Times|Div), v1, v2 ) if(isValue(v1) && isValue(v2)) =>{
        bop match{
          case Minus =>N(toNumber(v1) - toNumber(v2))
          case Times => N(toNumber(v1) * toNumber(v2))
          case Div => N(toNumber(v1) / toNumber(v2))
        }
      }

      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if (isValue(v1) && isValue(v2)) => B(inequalityVal(bop, v1, v2))

      case Binary(bop @ (Eq | Ne), v1, v2) if (isValue(v1) && isValue(v2)) => (v1, v2) match{

        case (Function(_, _, _), _) => throw DynamicTypeError(e)
        case (_,Function(_, _, _)) => throw DynamicTypeError(e)

        case (_,_) if (isValue(v1) && isValue(v2)) => bop match{

          case Eq => B(v1 == v2)
          case Ne => B(v1 != v2)

        }
      }

      case Binary(And, v1, e2) if isValue(v1) => if(toBoolean(v1)) e2 else v1

      case Binary(Or, v1, e2) if isValue(v1) => if(!toBoolean(v1)) e2 else v1

      case ConstDecl(x, e1, e2) if isValue(e1) => {
        substitute(e2, e1, x)
      }

      case If(e1,e2,e3) if(isValue(e1))=>{
        if(toBoolean(e1)) e2 else e3
      }

      case Call(v1, v2) if (isValue(v1) && isValue(v2)) => v1 match{
        case Function(None, m, ee) => {  //non-recursive
          substitute(ee, v2, m)
        }

        case Function(Some(f), x, code) => {   // Recursive
          substitute(substitute(code, v1, f), v2, x)
        }
        case _ => throw DynamicTypeError(e)
      }

      /*Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

        // ****** Your cases here
      case Unary(uop,e1) => Unary(uop,step(e1))

      case Binary(bop,e1,e2) => isValue(e1) match {

        case true => Binary(bop, e1, step(e2))
        case _ => Binary(bop, step(e1), e2)

      }

      case If(e1,e2,e3) => If(step(e1),e2,e3)

      case ConstDecl(x,e1,e2) => ConstDecl(x,step(e1),e2)

      case Call(e1, e2) => (e1,e2) match {
        case (Function(_, _, _), s2) =>  Call(e1, step(s2))
        case (s1,s2) => Call(step(s1),s2)
      }

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
