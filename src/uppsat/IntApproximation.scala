package uppsat

import uppsat.IntegerTheory._
import uppsat.ModelReconstructor.Model
import uppsat.PrecisionMap.Path
import uppsat.Encoder.PathMap

object IntApproximation extends Approximation[Int] {
  val inputTheory = IntegerTheory
  val outputTheory = IntegerTheory
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }

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
    
  // TODO: HACK, how do we construct the paths in an intelligent manner.
  def encodeIntegerSymbolPath(children : List[AST]) : List[Path] = {
    children.indices.map(List(_, 1)).toList
  }
     
  def encodeSymbolPath(symbol : ConcreteFunctionSymbol, children : List[AST], precision : Int) : List[Path] = {
    symbol match {
      case _ if children.isEmpty => List()
      case symbol : IntegerFunctionSymbol =>  encodeIntegerSymbolPath(children)
      case _ => children.indices.map(List(_)).toList   
    }    
  }    
      
  def encodeAux(ast : AST, path : Path, appPath : Path, pmap : PrecisionMap[Int], sourceToEncoding : PathMap) : (AST, PathMap) = {
    val AST(symbol, children) = ast
    val childrenPaths = encodeSymbolPath(symbol, children, pmap(path))
    val recCalls = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, i :: path, childrenPaths(i) ++ path, pmap, sourceToEncoding)
      }
    
    val newAST = encodeSymbol(symbol, recCalls.map(_._1), pmap(path))
    val newSTE = recCalls.map(_._2).foldLeft(sourceToEncoding + (path -> appPath))((x, y) => x ++ y)
    (newAST, newSTE)
  }
  
  def encode(ast : AST, pmap : PrecisionMap[Int]) : (AST, PathMap) = {
    encodeAux(ast, List(), List(), pmap, Map())     
  }
  
  def reconstruct(ast : AST, appModel : Model) : Model = {
    appModel
  }
}