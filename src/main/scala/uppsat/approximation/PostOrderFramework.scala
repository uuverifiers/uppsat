package uppsat.approximation

import uppsat.theory.Theory
import uppsat.ast.AST
import uppsat.ast.ConcreteSort
import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelReconstructor.Model
import uppsat.ModelReconstructor
import uppsat.Timer
import uppsat.globalOptions._
import uppsat.theory.FloatingPointTheory
import uppsat.theory.BooleanTheory.BoolTrue




class PostOrderNodeBasedApproximation(val appCore : ApproximationCore with ApproximationCodec with NodeByNodeReconstructor with RefinementStrategy) extends Approximation {
  
  type P = appCore.Precision
  val precisionOrdering = appCore.precisionOrdering
  val inputTheory = appCore.inputTheory
  val outputTheory = appCore.outputTheory
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) = 
    appCore.satRefine(ast, decodedModel, failedModel, pmap)
  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) = 
    appCore.unsatRefine(ast, core, pmap)
    
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }    
    appCore.encodeNode(ast, newChildren, pmap(ast.label))    
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), appCore.decodeNode)
    decodedModel
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()    
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, appCore.evaluateNode)
    reconstructedModel
  }
 

}


