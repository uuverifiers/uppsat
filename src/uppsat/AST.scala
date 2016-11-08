package uppsat

import BooleanTheory._
// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: What do we do with let-expressions.
// TODO: Sharing, how do we accommodate? Enforced sharing (seems like a bad idea?)
// TODO: We can use implicit conversion

// ASKPC: Is this a good way? (syntactic sugar)
// DD: 1) "Cannot" inherit case classes
//     2) Typing the AST messed up matching with Node (e.g., in translator)
abstract class Node(val symbol : ConcreteFunctionSymbol) {
  
  def &(that : Node) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (BooleanSort, BooleanSort) => boolAnd(this, that)
     }
  }
  
  def unary_! = {
     this.symbol.sort match {
       case BooleanSort => boolNot(this)
     }
  }
  
}
case class InternalNode(override val symbol : ConcreteFunctionSymbol, desc : Seq[Node]) extends Node(symbol)
case class LeafNode(override val symbol : ConcreteFunctionSymbol) extends Node(symbol)