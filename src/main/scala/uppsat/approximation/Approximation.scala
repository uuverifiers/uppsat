package uppsat.approximation

import uppsat.theory.Theory
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ModelEvaluator.Model
import uppsat.precision.PrecisionMap


class Approximation(val context : ApproximationContext
                        with Codec
                        with ModelReconstruction
                        with ProofGuidedRefinementStrategy
                        with ModelGuidedRefinementStrategy
                        ) {
  type P = context.Precision
  val precisionOrdering : PrecisionOrdering[P] = context.precisionOrdering
  val inputTheory : Theory = context.inputTheory
  val outputTheory : Theory = context.outputTheory
  
  // General framework primitives
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] =
    context.satRefine(ast, decodedModel, failedModel, pmap)
  
  def unsatRefine(ast : AST, unsatCore : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] =
    context.unsatRefine(ast, unsatCore, pmap)

  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST =
    context.encodeFormula(ast, pmap)

  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) : Model =
    context.decodeModel(ast, appModel, pmap)

  def reconstruct(ast : AST, decodedModel : Model) : Model =
    context.reconstruct(ast, decodedModel)
 }


trait ApproximationContext {
  val inputTheory : Theory
  val outputTheory : Theory

  type Precision
  val precisionOrdering : PrecisionOrdering[Precision]
}

trait Codec extends ApproximationContext {
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST
  def decodeModel(ast : AST, appMode : Model, pmap : PrecisionMap[Precision]) : Model
}

trait ModelReconstruction extends ApproximationContext {
  def reconstruct(ast : AST, decodedModel : Model) : Model
}

trait ModelGuidedRefinementStrategy extends ApproximationContext {
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

trait ProofGuidedRefinementStrategy extends ApproximationContext {
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

trait RefinementStrategy extends ModelGuidedRefinementStrategy 
                            with ProofGuidedRefinementStrategy



