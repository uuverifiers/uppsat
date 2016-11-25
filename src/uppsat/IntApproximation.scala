package uppsat

import uppsat.IntegerTheory._
import uppsat.PrecisionMap.Path

object IntApproximation extends Approximation[Int] {
  val inputTheory = IntegerTheory
  val outputTheory = IntegerTheory
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
//  def unsatRefine(precision : Int) = precision + 1
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
  
  def encodeIntegerSymbol( symbol : ConcreteFunctionSymbol, children : List[AST], precision : Int) : AST = {
      val cond = new AST(symbol, children) <= precision
      val newAST = AST(IntITE, List(cond, new AST(symbol, children), precision))
      newAST
    }
    
    
    def encodeSymbol(symbol : ConcreteFunctionSymbol, children : List[AST], precision : Int) : AST = {
      symbol match {
        case _ if children.isEmpty => AST(symbol)
        case symbol : IntegerFunctionSymbol =>  encodeIntegerSymbol(symbol, children, precision)
        case symbol : IntegerPredicateSymbol => new AST(symbol, children)        
        case symbol => new AST(symbol, children)
      }    
    }
      
    def encodeAux(ast : AST, prefix : Path, pmap : PrecisionMap[Int], sourceToEncoding : Map[AST, AST]) : (AST, Map[AST, AST]) = {
      val (symbol, children) = (ast.symbol, ast.children)
      var ste = sourceToEncoding
      val newChildren = 
        for ((c, i) <- children zip children.indices) yield {
          val (newChild, newSte) = encodeAux( c, i :: prefix, pmap, ste)
          ste = newSte
          newChild
        }
      val newAST = encodeSymbol(symbol, newChildren, pmap(prefix))
      (newAST, ste + (ast -> newAST))
    }
    
    def encode(ast : AST, pmap : PrecisionMap[Int]) : (AST, Map[AST, AST]) = {
      encodeAux(ast, List(), pmap, Map())
    }
    
    def reconstruct(ast : AST, appModel : Model) : Model = {
      appModel
    }
}