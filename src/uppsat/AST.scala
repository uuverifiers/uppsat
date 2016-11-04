package uppsat

// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: What do we do with let-expressions.
// TODO: Sharing, how do we accommodate? Enforced sharing (seems like a bad idea?)
// TODO: We can use implicit conversion
object AST {  
  abstract class Node(symbol : FunctionSymbol)
  case class InternalNode(symbol : FunctionSymbol, desc : Seq[Node]) extends Node(symbol)
  case class LeafNode(symbol : FunctionSymbol) extends Node(symbol)  
}