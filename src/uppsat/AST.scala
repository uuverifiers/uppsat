package uppsat

object AST {  
  abstract class Node(symbol : FunctionSymbol)
  case class InternalNode(symbol : FunctionSymbol, desc : Seq[Node]) extends Node(symbol)
  case class LeafNode(symbol : FunctionSymbol) extends Node(symbol)  
}