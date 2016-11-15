package uppsat

import uppsat.IntegerTheory._

class Encoder[T] {
  var nodeMap = Map() : Map[Node, Node]
  
    def precisionToInt(p : T) = {
      p.asInstanceOf[Int]      
    }
    
    def encodeAddition( symbol : ConcreteFunctionSymbol, desc : Seq[Node], precision : T) : Node = {
      val cond = new InternalNode(symbol, desc) <= precisionToInt(precision)
      val newNode = InternalNode(IntITE, List(cond, new InternalNode(symbol, desc), precisionToInt(precision)))
      newNode
    }
    
    def encodeSymbol( symbol : ConcreteFunctionSymbol, desc : Seq[Node], precision : T) : Node = {
      symbol match {
        case _ if desc.isEmpty => LeafNode(symbol)
        case symbol : IntegerFunctionSymbol =>  encodeAddition(symbol, desc, precision)
        case symbol : IntegerPredicateSymbol => new InternalNode(symbol, desc)        
        case symbol => new InternalNode(symbol, desc)
      }    
    }
      
    def encodeAux(ast : Node, pmap : PrecisionMap[T]) : Node = {
      val newNode = 
        ast match {
          case InternalNode(symbol, desc) => encodeSymbol(symbol, desc.map(encodeAux(_,pmap)), pmap(ast))
          case LeafNode(symbol) => encodeSymbol(symbol, List.empty, pmap(ast))
        }
      nodeMap += ast -> newNode
      newNode
    }
    
    def encode(ast : Node, pmap : PrecisionMap[T]) : (Node, Map[Node, Node]) = {
      val newAst = encodeAux(ast, pmap)
      (newAst, nodeMap)
    }
}