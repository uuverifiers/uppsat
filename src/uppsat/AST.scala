package uppsat

import BooleanTheory._
import IntegerTheory._
import scala.collection.mutable.ArrayStack

object Leaf {
  def apply[D](d : D) = Tree(d, List())
  def unapply[D](t : Tree[D]) : Option[D] = t match {
    case Tree(d, List()) => Some(d)
    case _ => None
  }
}

case class Tree[D](d : D, children : List[Tree[D]]) {
  def map[E](f : D => E) : Tree[E] = {
    val newD = f(d)
    Tree(newD, children map (_ map f))
  }
  def mapUpDown(f : D => D) : Tree[D] = {
    val newD = f(d)
    val newChildren = children map (_ map f)
    Tree(f(newD), newChildren)
  }
  def foreach[U](f : D => U) : Unit = {
    f(d)
    for (c <- children) c foreach f
  }
  def zip[E](t : Tree[E]) : Tree[(D, E)] = t match {
    case Tree(e, children2) =>
      Tree((d, e),
           for ((c1, c2) <- children zip children2)
           yield (c1 zip c2))
  }
  def unzip[D1, D2](implicit asPair: D => (D1, D2)): (Tree[D1], Tree[D2]) = {
    val (children1, children2) = (for (c <- children) yield c.unzip).unzip
    val (d1, d2) = asPair(d)
    (Tree(d1, children1), Tree(d2, children2))
  }
  def subtrees : Tree[Tree[D]] =
    Tree(this, for (c <- children) yield c.subtrees)
  def toList : List[D] = iterator.toList
  def toSeq = toList
  def toSet = iterator.toSet
  def iterator = new Iterator[D] {
    val todo = new ArrayStack[Tree[D]]
    todo push Tree.this
    def hasNext = !todo.isEmpty
    def next = {
      val Tree(data, children) = todo.pop
      todo ++= children
      data
    }
  }

  def prettyPrint : Unit =
    prettyPrint("")

  def prettyPrint(indent : String) : Unit = {
    val newIndent = indent + "   "
    println(indent + d)
    for (c <- children) (c prettyPrint newIndent)
  }

  def size = iterator.size
}


object AST {
  def apply(symbol : ConcreteFunctionSymbol, children : List[AST]) = new AST(symbol, children)
  def apply(symbol : ConcreteFunctionSymbol) = new AST(symbol, List())
  
  
  def unapply(t : AST) : Option[(ConcreteFunctionSymbol, List[AST])] = 
    Some((t.symbol, t.children))
}

class AST(val symbol : ConcreteFunctionSymbol, override val children : List[AST]) extends Tree[ConcreteFunctionSymbol](symbol, children) {

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
// DD: 1) "Cannot" inherit case classes
//     2) Typing the AST messed up matching with AST (e.g., in translator)
