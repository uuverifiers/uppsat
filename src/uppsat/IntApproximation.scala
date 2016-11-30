package uppsat

import uppsat.IntegerTheory._
import uppsat.ModelReconstructor.Model
import uppsat.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.AST.Label

object IntApproximation extends Approximation[Int] {
  val inputTheory = IntegerTheory
  val outputTheory = IntegerTheory
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
  
  def encodeIntegerSymbol( symbol : ConcreteFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
      val cond =  AST(symbol, children) <= precision
      val newAST = AST(IntITE, path, List(cond, AST(symbol, children), precision))
      newAST
    }
      
  def encodeSymbol(symbol : ConcreteFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
    symbol match {
      case _ if children.isEmpty => Leaf(symbol, path)
      case symbol : IntegerFunctionSymbol =>  encodeIntegerSymbol(symbol, path, children, precision)
      case symbol : IntegerPredicateSymbol => AST(symbol, path, children)        
      case symbol => AST(symbol, path, children)
    }    
  }
    
  def encodeAux(ast : AST, path : Path, pmap : PrecisionMap[Int]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, i :: path, pmap)
      }    
    encodeSymbol(symbol, path, newChildren, pmap(path))    
  }
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Int]) : AST = {
    encodeAux(ast, List(0), pmap)
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    appModel
  }
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    decodedModel
  }
}