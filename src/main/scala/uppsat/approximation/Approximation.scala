package uppsat.approximation

import uppsat.ModelEvaluator.Model
import uppsat.ast.AST
import uppsat.theory.Theory
import uppsat.precision.{PrecisionMap, PrecisionOrdering}

/** The core object of an approximation which must be extended with a context.
  *
  *
  */
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

  /** Refines ast based on the difference between {@code decodedModel} and {@code failedModel}.
    *
    */
  def satRefine(ast : AST,
                decodedModel : Model,
                failedModel : Model,
                pmap : PrecisionMap[P]) : PrecisionMap[P] =
    context.satRefine(ast, decodedModel, failedModel, pmap)

  /** Refines ast based on the {@code unsatCore}.
    *
    */
  def unsatRefine(ast : AST,
                  unsatCore : List[AST],
                  pmap : PrecisionMap[P]) : PrecisionMap[P] =
    context.unsatRefine(ast, unsatCore, pmap)

  /** Encodes formula in {@code ast} using precision map {@code pmap}.
    *
    */
  def encodeFormula(ast : AST,
                    pmap : PrecisionMap[P]) : AST =
    context.encodeFormula(ast, pmap)

  /** Decodes model {@code appModel}.
    *
    */
  def decodeModel(ast : AST,
                  appModel : Model,
                  pmap : PrecisionMap[P]) : Model =
    context.decodeModel(ast, appModel, pmap)

  /** Tries to reconstruct {@code decodedModel}.
    *
    */
  def reconstruct(ast : AST,
                  decodedModel : Model) : Model =
    context.reconstruct(ast, decodedModel)
 }


/** A context gives types to input/output theory and precision(ordering).
  * 
  */
trait ApproximationContext {
  val inputTheory : Theory
  val outputTheory : Theory

  type Precision
  val precisionOrdering : PrecisionOrdering[Precision]
}

/** A codec describes how to encode formulas and decode models.
  *
  */
trait Codec extends ApproximationContext {
  /** Encodes formula in {@code ast} using precision map {@code pmap}.
    *
    */
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST

  /** Decodes model {@code appModel}.
    *
    */
  def decodeModel(ast : AST,
                  appMode : Model,
                  pmap : PrecisionMap[Precision]) : Model
}

/** Describes how to do model reconstruction.
  *
  */
trait ModelReconstruction extends ApproximationContext {
  /** Tries to reconstruct {@code decodedModel}.
    *
    */
  def reconstruct(ast : AST, decodedModel : Model) : Model
}

/** Describes how to do refinement at false positives.
  *
  */
trait ModelGuidedRefinementStrategy extends ApproximationContext {
  /** Refines ast based on the difference between {@code decodedModel} and {@code failedModel}.
    *
    */
  def satRefine(ast : AST,
                decodedModel : Model,
                failedModel : Model,
                pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

/** Describes how to do refinement on negative results.
  *
  */
trait ProofGuidedRefinementStrategy extends ApproximationContext {
  /** Refines ast based on the {@code unsatCore}.
    *
    */
  def unsatRefine(ast : AST,
                  core : List[AST],
                  pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
}

/** A refinement strategy consists of model guided and proof guided refinement.
  *
  */
trait RefinementStrategy extends ModelGuidedRefinementStrategy
                            with ProofGuidedRefinementStrategy



