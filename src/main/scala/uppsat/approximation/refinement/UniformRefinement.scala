package uppsat.approximation.refinement

import uppsat.approximation._
import uppsat.ast.AST
import uppsat.precision._
import uppsat.ModelEvaluator.Model

trait UniformPGRefinementStrategy extends ProofGuidedRefinementStrategy {
  def unsatRefinePrecision(p : Precision) : Precision
  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    pmap.map(unsatRefinePrecision)
  }
}


trait UniformMGRefinementStrategy extends ModelGuidedRefinementStrategy {
  def satRefinePrecision(p : Precision) : Precision

  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])  = {
    pmap.map(satRefinePrecision)
  }  
}

trait UniformRefinementStrategy extends UniformMGRefinementStrategy
                                   with UniformPGRefinementStrategy {
  def increasePrecision(p : Precision) : Precision
  
  def satRefinePrecision(p : Precision) = increasePrecision(p)
  
  def unsatRefinePrecision(p : Precision) = increasePrecision(p)
}