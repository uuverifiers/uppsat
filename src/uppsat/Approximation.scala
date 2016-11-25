package uppsat

import uppsat.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model

trait Approximation[T] {
  
  val inputTheory : Theory
  val outputTheory : Theory
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[T]) : PrecisionMap[T]  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[T]) : PrecisionMap[T]
  def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, PathMap) 
  def reconstruct(ast : AST, appModel : Model) : Model
  
  //up/down
  //castingFunction (sort, precision, precision)
  //refinementFunctions for SAT/UNSAT cases
  //errorFunction
 }

