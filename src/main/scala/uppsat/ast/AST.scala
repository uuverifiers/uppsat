package uppsat.ast

import uppsat.theory.BooleanTheory._
import uppsat.ModelReconstructor.Model
import scala.collection.mutable.ArrayStack
import uppsat.precision.PrecisionMap.Path
import uppsat.theory.IntegerTheory._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.ast.AST._

object Leaf {
  def apply(symbol : ConcreteFunctionSymbol) = new AST(symbol, List(), List())
  def apply(d : ConcreteFunctionSymbol, label : Label ) = AST(d, label, List())
  def unapply(t : AST) : Option[(ConcreteFunctionSymbol, Label)] = t match {
    case AST(d, label, List()) => Some((d, label))
    case _ => None
  }
} 

object AST {
  type Label = Path
  def apply(symbol : ConcreteFunctionSymbol, children : List[AST]) = new AST(symbol, List(), children)
  
  def postVisit[A]( ast : AST, accumulator : A,  work : (A, AST) => A ) : A = {
    val AST(symbol, label, children) = ast
    var accu = accumulator
   
    for ((c, i) <- children zip children.indices) 
      accu = postVisit( c, accu, work)
    
    work(accu, ast)
  }
  
  def postVisit[A,B]( ast : AST, accumulator : A, args : B,  work : (B, A, AST) => A ) : A = {
    val AST(symbol, label, children) = ast
    var accu = accumulator
   
    for (c <- children) 
      accu = postVisit( c, accu, args, work)
    
    work(args, accu, ast)
  }


def boolVisit[T]( ast : AST, accumulator : T, cond : (T, AST, Path) => Boolean, work : (T, AST) => T ) : T = {
    val AST(symbol, label, children) = ast
    var accu = accumulator
    
    if (cond(accu, ast, label)) {
      accu = work(accu, ast)
      
      for (c <- children) 
        accu = boolVisit( c, accu, cond, work)
    }
    accu
  }
}

case class AST(val symbol : ConcreteFunctionSymbol, val label : Label, val children : List[AST]) {
  
  // Copied TREE, some of these functions might not make sense when we introduce more kinds of nodes
  // i.e., Quantifiers...
  
  def getPath(path : Path) = {
    def getPathAux(ast : AST, p : Path) : AST = {
      p match {
        case Nil => ast
        case h :: t => getPathAux(ast.children(h), p.tail) 
      }
    }
    getPathAux(this, path.reverse.tail)
  }
  
  def apply(path : Path) : AST = getPath(path)
  
  def map(f : ConcreteFunctionSymbol => ConcreteFunctionSymbol) : AST = {
      AST(f(symbol), label, children map (_ map f))
    }

  def foreach[U](f : ConcreteFunctionSymbol => U) : Unit = {
    f(symbol)
    for (c <- children) c foreach f
  }
  
  
  // Note: Dual use of path/label
  def labelAux(path: Path) : AST = {    
    if (label != List()) 
      throw new Exception("Trying to label an already labeled AST")
    
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield { 
      c.labelAux( i :: path)
    }
    AST(symbol, path, newChildren)
  }
  
  def labelAST : AST = {
     this.labelAux(List(0))
  }
  
  def iterator = new Iterator[AST] {
    val todo = new ArrayStack[AST]
    todo push (AST.this)
    def hasNext = !todo.isEmpty
    def next = {
      val n = todo.pop
      todo ++= n.children
      n
    }
  }
    
  def toSet = iterator.toSet 
    
  def prettyPrint : Unit =
    prettyPrint("")
    
  def prettyPrint(indent : String) : Unit = {
    val newIndent = indent + "   "
    println(indent + symbol + " [" + label.mkString(",") + "] //" + symbol.sort)
    for (c <- children) (c prettyPrint newIndent)
  }
  
  def ppWithModels(indent : String, smallModel : Model, bigModel : Model) : Unit = {
    val newIndent = indent + "   "
    this.symbol.sort match {
      case BooleanSort if (smallModel(this) == bigModel(this)) => ()
      case _ => { 
          println(indent + symbol + " [" + label.mkString(",") + "] //" + symbol.sort + " " + smallModel(this).symbol + " -> " + bigModel(this).symbol)
          for (c <- children) (c ppWithModels(newIndent, smallModel, bigModel) )
      }
    }
    
  }
  
  def size = iterator.size  
  
  
  def symbols : Set[ConcreteFunctionSymbol]= this.toSet.map(_.symbol)
  
  def isVariable = {
    symbol.theory.isVariable(symbol)
  }
  
  //
  //  Syntactic sugar
  //
  def &(that : AST) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (BooleanSort, BooleanSort) => boolAnd(this, that)
     }
  }
  
  def unary_! = {
     this.symbol.sort match {
       case BooleanSort => boolNot(this)
     }
  }
  
  def unary_- = {
     this.symbol.sort match {
       case f : FPSort => floatNegate(this)
     }
  }
  
  def +(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatAddition(this, that)       
     }
  }
  
  def -(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intSubstraction(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatSubtraction(this, that)
     }
  }
  
  def *(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatMultiplication(this, that)       
     }
  }
  
  def /(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatDivision(this, that)       
     }
  }
  
  //TODO: Check which one to use
  def ===(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (BooleanSort, BooleanSort) => boolEquality(this, that)
      case (IntegerSort, IntegerSort) => intEquality(this, that)
      case (f1 : FPSort, f2 : FPSort) => floatEquality(this, that)
      case (RoundingModeSort, RoundingModeSort) => rmEquality(this, that)
     }
  }
  
  def <=(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intLessThanOrEqual(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatLessThanOrEqual(this, that)
     }
  }
  
  def <(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intLessThan(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatLessThan(this, that)
     }
  }
  
  def >=(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intLessThanOrEqual(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatGreaterThanOrEqual(this, that)
     }
  }
  
  def >(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intLessThan(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatGreaterThan(this, that)
     }
  }
  
  
}



// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: What do we do with let-expressions.
// TODO: Sharing, how do we accommodate? Enforced sharing (seems like a bad idea?)
// TODO: We can use implicit conversion

// ASKPC: Is this a good way? (syntactic sugar)
