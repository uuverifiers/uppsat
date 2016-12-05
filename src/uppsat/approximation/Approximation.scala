package uppsat.approximation

import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.theory.Theory

trait Approximation[T] {
  
  val inputTheory : Theory
  val outputTheory : Theory
  val precisionOrdering : PrecisionOrdering[T]
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[T]) : PrecisionMap[T]  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[T]) : PrecisionMap[T]
  def encodeFormula(ast : AST, pmap : PrecisionMap[T]) : AST
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[T]) : Model
  def reconstruct(ast : AST, decodedModel : Model) : Model
  
 }

trait TemplateApproximation[T] extends Approximation[T] {
  
  //up/down
  //castingFunction (sort, precision, precision)
  //errorFunction
  //nodeByNodeTranslationFunctions
}
