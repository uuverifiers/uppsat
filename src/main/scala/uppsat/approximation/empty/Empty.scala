package uppsat.approximation.empty

import uppsat.ModelEvaluator.Model
import uppsat.approximation.ApproximationContext
import uppsat.approximation.codec.EmptyCodec
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.refinement.
  {UniformPGRefinementStrategy, UniformMGRefinementStrategy}
import uppsat.precision.{IntPrecisionOrdering, PrecisionMap}
import uppsat.theory.EmptyTheory

/** Empty theory for using backend solver */
trait EmptyContext extends ApproximationContext {
  type Precision = Int
  val precisionOrdering = new IntPrecisionOrdering(0,0)
  val inputTheory = EmptyTheory
  val outputTheory = EmptyTheory
}

trait EmptyPGRefinementStrategy extends UniformPGRefinementStrategy {
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
}

trait EmptyMGRefinementStrategy extends UniformMGRefinementStrategy {
  def satRefinePrecision( p : Int) : Int = {
    p + 1
  }

}

object EmptyApp extends EmptyContext
    with EmptyCodec
    with EmptyReconstruction
    with EmptyMGRefinementStrategy
    with EmptyPGRefinementStrategy
