package uppsat


trait Approximation[T] {
  type Model = Map[AST, AST]
  
  val inputTheory : Theory
  val outputTheory : Theory
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[T]) : PrecisionMap[T]  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[T]) : PrecisionMap[T]
  def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, Map[AST, AST]) 
  def reconstruct(ast : AST, appModel : Model) : Model
  
  //up/down
  //castingFunction (sort, precision, precision)
  //refinementFunctions for SAT/UNSAT cases
  //errorFunction
  //satRefine(node, appModel, candidateModel, precision : T) : T = 
  //unsatRefine() 
}

