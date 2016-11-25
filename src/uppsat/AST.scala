package uppsat

import BooleanTheory._
import IntegerTheory._
import scala.collection.mutable.ArrayStack
import uppsat.PrecisionMap.Path

object Leaf {
  def apply(d : ConcreteFunctionSymbol) = AST(d, List())
  def unapply(t : AST) : Option[ConcreteFunctionSymbol] = t match {
    case AST(d, List()) => Some(d)
    case _ => None
  }
} 

object AST {
  def apply(symbol : ConcreteFunctionSymbol) = new AST(symbol, List())

}

case class AST(val symbol : ConcreteFunctionSymbol, val children : List[AST]) {

  
  // Copied TREE, some of these functions might not make sense when we introduce more kinds of nodes
  // i.e., Quantifiers...
  
  def getPath(path : Path) = {
    def getPathAux(ast : AST, p : Path) : AST = {
      p match {
        case Nil => ast
        case h :: t => getPathAux(ast.children(h), p.tail) 
      }
    }
    getPathAux(this, path.reverse)
  }
  
  def apply(path : Path) : AST = getPath(path)
  
  def map(f : ConcreteFunctionSymbol => ConcreteFunctionSymbol) : AST = {
      AST(f(symbol), children map (_ map f))
    }

  def foreach[U](f : ConcreteFunctionSymbol => U) : Unit = {
    f(symbol)
    for (c <- children) c foreach f
  }
  
  def iterator = new Iterator[ConcreteFunctionSymbol] {
    val todo = new ArrayStack[AST]
    todo push AST.this
    def hasNext = !todo.isEmpty
    def next = {
      val AST(data, children) = todo.pop
      todo ++= children
      data
    }
  }
  
  
  def toSet = iterator.toSet 
    
  def prettyPrint : Unit =
    prettyPrint("")
  
  def prettyPrint(indent : String) : Unit = {
    val newIndent = indent + "   "
    println(indent + symbol)
    for (c <- children) (c prettyPrint newIndent)
  }
  
  def size = iterator.size  
  
  
  def symbols : Set[ConcreteFunctionSymbol]= this.toSet    
  
  //Syntactic sugar
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
  
  def +(that : AST) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intAddition(this, that)
     }
  }
  
  def -(that : AST) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intSubstraction(this, that)
     }
  }
  
  //TODO: Check which one to use
  def ===(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intEquality(this, that)
     }
  }
  
  def <=(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intLessThanOrEqual(this, that)
     }
  }
}



// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: What do we do with let-expressions.
// TODO: Sharing, how do we accommodate? Enforced sharing (seems like a bad idea?)
// TODO: We can use implicit conversion

// ASKPC: Is this a good way? (syntactic sugar)
