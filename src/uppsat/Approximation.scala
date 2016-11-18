package uppsat

trait Approximation[T] {
  val inputTheory : Theory
  val outputTheory : Theory
  def refine(precision : T) : T
  
  //up/down
  //castingFunction (sort, precision, precision)
  //refinementFucntions for SAT/UNSAT cases
  //errorFunction
  //satRefine(node, appModel, candidateModel, precision : T) : T = 
  //unsatRefine() 
}