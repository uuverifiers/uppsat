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

class AnalyticalFramework(val appCore : ApproximationCore 
                                         with ApproximationCodec 
                                         with FixpointReconstruction 
                                         with ErrorBasedRefinementStrategy) extends Approximation {

  type P = appCore.Precision
  val precisionOrdering = appCore.precisionOrdering
  val inputTheory = appCore.inputTheory
  val outputTheory = appCore.outputTheory
  
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
      appCore.reconstruct(ast, decodedModel)
  }
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] = {
//    val accu = Map[AST, Double]()
//    val errorRatios = AST.postVisit(ast, accu, appCore.nodeError(decodedModel)(failedModel))
//    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
//    val k = math.ceil(appCore.fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
 
    
    val critical = appCore.retrieveCriticalAtoms(decodedModel)(ast).map(_.iterator).flatten.toList
    val nodesToRefine = critical.filter( x => decodedModel(x) != failedModel(x))
    
    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter( x => appCore.precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision))) { 
      newPMap = newPMap.update(node.label, appCore.satRefinePrecision(node, newPMap))
      changes += 1      
    }
    
    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap    
  }
  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    pmap.map(appCore.unsatRefinePrecision)
  }

  
}
