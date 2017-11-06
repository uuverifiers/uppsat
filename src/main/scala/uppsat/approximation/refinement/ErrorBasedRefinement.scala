package uppsat.approximation.refinement

import uppsat.ast.AST
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.precision._
import uppsat.approximation.toolbox.Toolbox
import uppsat.globalOptions._

// Error based refinement strategy uses a measure of error to
// determine which precisions need to be refined
// TODO: (Aleks) "Magic" numbers, I don't understand them
trait ErrorBasedRefinementStrategy extends PostOrderRefinement {
  val topK : Int // TODO: (Aleks) Should this be int or precision? RE: It should be int
  val fractionToRefine : Double
  val precisionIncrement : Precision

  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]
    override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])
      : PrecisionMap[Precision] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
      //    debug(errorRatios.mkString("\n"))
      //    debug(errorRatios.getClass)

    // TODO: (Aleks) Is this correct?ErrorBasedRefinementStrategy
    def compareFloatsWithSpecialNumbers(f1 : Double, f2: Double) : Boolean = {
      val d1 = f1.doubleValue()
      val d2 = f2.doubleValue()
      d1.compareTo(d2) > 0
    }

    val sortedErrRatios = errorRatios.toList.sortWith((x, y) => compareFloatsWithSpecialNumbers(x._2, y._2))
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions

    val relevantNodes = Toolbox.booleanComparisonOfModels(ast, decodedModel, failedModel)
    val nodesToRefine = sortedErrRatios.filter( x => relevantNodes.contains(x._1)).map(_._1)

    var newPMap = pmap
    var changes = 0
    for (node <-
         nodesToRefine.filter(
           x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)
         ).take(k)) {
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1
    }

    if (changes == 0) {
      // all the nodes where evaluation fails are at full precision.
      // UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap
  }
}