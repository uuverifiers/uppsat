package uppsat

trait Approximation[T] {
  val inputTheory : Theory
  val outputTheory : Theory
  def refine(precision : T) : T
  def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, Map[AST, AST]) 
  
  //up/down
  //castingFunction (sort, precision, precision)
  //refinementFunctions for SAT/UNSAT cases
  //errorFunction
  //satRefine(node, appModel, candidateModel, precision : T) : T = 
  //unsatRefine() 
}