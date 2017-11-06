package uppsat.approximation

import uppsat.theory.Theory
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ModelEvaluator.Model
import uppsat.precision.PrecisionMap


class Approximation(val core : ApproximationCore
                        with Codec
                        with ModelReconstruction
                        with ProofGuidedRefinementStrategy
                        with ModelGuidedRefinementStrategy
                        ) {
  type P = core.Precision
  val precisionOrdering : PrecisionOrdering[P] = core.precisionOrdering
  val inputTheory : Theory = core.inputTheory
  val outputTheory : Theory = core.outputTheory
  
  // General framework primitives
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] =
    core.satRefine(ast, decodedModel, failedModel, pmap)
  
  def unsatRefine(ast : AST, unsatCore : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] =
    core.unsatRefine(ast, unsatCore, pmap)

  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST =
    core.encodeFormula(ast, pmap)

  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) : Model =
    core.decodeModel(ast, appModel, pmap)

  def reconstruct(ast : AST, decodedModel : Model) : Model =
    core.reconstruct(ast, decodedModel)
 }


trait ApproximationCore {
  val inputTheory : Theory
  val outputTheory : Theory

  type Precision
  val precisionOrdering : PrecisionOrdering[Precision]
}

trait Codec extends ApproximationCore {
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST
  def decodeModel(ast : AST, appMode : Model, pmap : PrecisionMap[Precision]) : Model
}

trait ModelReconstruction extends ApproximationCore {
  def reconstruct(ast : AST, decodedModel : Model) : Model
}

trait ModelGuidedRefinementStrategy extends ApproximationCore {
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

trait ProofGuidedRefinementStrategy extends ApproximationCore {
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

trait RefinementStrategy extends ModelGuidedRefinementStrategy 
                            with ProofGuidedRefinementStrategy



