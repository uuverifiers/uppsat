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
    
    // TODO: HACK
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
      var ste = sourceToEncoding
      val newChildren = 
        for ((c, i) <- children zip children.indices) yield {
          val (newChild, newSte) = encodeAux( c, i :: path, childrenPaths(i) ++ path, pmap, ste)
          ste = newSte
          newChild
        }
      val newAST = encodeSymbol(symbol, newChildren, pmap(path))
      (newAST, ste + (path -> appPath))
    }
    
    def encode(ast : AST, pmap : PrecisionMap[Int]) : (AST, PathMap) = {
      val (newAst, pm) = encodeAux(ast, List(), List(), pmap, Map())     
      (newAst, pm)
    }
    
    def reconstruct(ast : AST, appModel : Model) : Model = {
      appModel
    }
}