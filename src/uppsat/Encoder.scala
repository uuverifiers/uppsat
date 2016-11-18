package uppsat

import uppsat.IntegerTheory._
import uppsat.PrecisionMap.Path

class Encoder[T] {
  var sourceToEncoding = Map() : Map[AST, AST]
  
    def precisionToInt(p : T) = {
      p.asInstanceOf[Int]      
    }
    
    def encodeIntegerSymbol( symbol : ConcreteFunctionSymbol, children : List[AST], precision : T) : AST = {
      val cond = new AST(symbol, children) <= precisionToInt(precision)
      val newAST = AST(IntITE, List(cond, new AST(symbol, children), precisionToInt(precision)))
      newAST
    }
    
    def encodeSymbol( symbol : ConcreteFunctionSymbol, children : List[AST], precision : T) : AST = {
      symbol match {
        case _ if children.isEmpty => AST(symbol)
        case symbol : IntegerFunctionSymbol =>  encodeIntegerSymbol(symbol, children, precision)
        case symbol : IntegerPredicateSymbol => new AST(symbol, children)        
        case symbol => new AST(symbol, children)
      }    
    }
      
    def encodeAux(ast : AST, prefix : Path, pmap : PrecisionMap[T]) : AST = {
      val (symbol, children) = (ast.symbol, ast.children)
      val newChildren = 
        for ((c, i) <- children zip children.indices) yield 
          encodeAux( c, i :: prefix, pmap)          
      val newAST = encodeSymbol(symbol, newChildren, pmap(prefix))
      sourceToEncoding += ast -> newAST //TODO: do it with an acumulator
      newAST
    }
    
    def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, Map[AST, AST]) = {
      val newAst = encodeAux(ast,List(), pmap)
      (newAst, sourceToEncoding)
    }
}