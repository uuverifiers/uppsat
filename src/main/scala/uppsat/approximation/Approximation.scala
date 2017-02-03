package uppsat.approximation

import uppsat.theory.Theory
import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap

trait Approximation {
  type P
  val precisionOrdering : PrecisionOrdering[P] 
  val inputTheory : Theory
  val outputTheory : Theory
  
  // General framework primitives
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P]  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P]
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) : Model
  def reconstruct(ast : AST, decodedModel : Model) : Model
 }



