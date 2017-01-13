package uppsat.approximation

import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ast.ConcreteSort
import uppsat.theory.Theory
import uppsat.precision.PrecisionOrdering
import uppsat.ast._
import uppsat.precision.PrecisionMap.Path

trait Approximation {
  type P
  // Do we need this? 
  val inputTheory : Theory
  val outputTheory : Theory
  val precisionOrdering : PrecisionOrdering[P]
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P]  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P]
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) : Model
  def reconstruct(ast : AST, decodedModel : Model) : (Model, Map[ConcreteFunctionSymbol, AST])
  
 }



trait TemplateApproximation extends Approximation {  
  def encodeNode(symbol : FunctionSymbol, children : List[AST], precision : P) : AST
  def cast(ast : AST, source : ConcreteSort, target : ConcreteSort  ) : AST
  //errorFunction
  //nodeByNodeTranslationFunctions
  
  def encodeAux(ast : AST, path : Path, pmap : PrecisionMap[P]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, i :: path, pmap)
      }    
    val AST(functionSymbol, _, encChildren) = encodeNode(symbol, newChildren, pmap(path))
    AST(functionSymbol, path, encChildren)
  }
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST = {
    encodeAux(ast, List(0), pmap)
  }
}
