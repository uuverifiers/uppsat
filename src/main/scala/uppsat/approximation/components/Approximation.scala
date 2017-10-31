package uppsat.approximation.components

import uppsat.theory.Theory
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap
import uppsat.approximation._

class Approximation(val core : ApproximationCore
                        with Codec
                        with ModelReconstructor
                        with RefinementStrategy) {
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



