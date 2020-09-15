package uppsat.approximation.refinement

import uppsat.ast.AST
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.precision._
import uppsat.approximation.toolbox.Toolbox
import uppsat.globalOptions._

trait PostOrderRefinement extends ModelGuidedRefinementStrategy {
  def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision]) : Precision

  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    val critical = Toolbox.retrieveCriticalAtoms(decodedModel)(ast).map(_.iterator).flatten.toList
    val nodesToRefine = critical.filter( x => decodedModel(x) != failedModel(x))

    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter
         ( x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision))) {
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1
    }

    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      // TODO: unsatRefine should be replaced by some naive increment...
      throw new Exception("PostOrderRefinement failed...")
      // newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap
  }
}
