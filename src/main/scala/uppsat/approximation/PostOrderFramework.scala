package uppsat.approximation

import uppsat.theory.Theory
import uppsat.ast.AST
import uppsat.ast.ConcreteSort
import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelReconstructor.Model

trait ApproximationCore[P] {
  val inputTheory : Theory
  val outputTheory : Theory
  
  type Precision  = P
  val precisionOrdering : PrecisionOrdering[Precision]
  
  
}

trait NodeOps[P] {
  def encodeNode(ast : AST, children : List[AST], precision : P) : AST //Codec
  def decodeNode( args : (Model, PrecisionMap[P]), decodedModel : Model, ast : AST) : Model
  def cast(ast : AST, target : ConcreteSort  ) : AST // PrecisionOrdering ?
  
  def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy 
  
   
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]
  def satRefinePrecision( node : AST, pmap : PrecisionMap[P]) : P
}


class PostOrderFramework(appCore : ApproximationCore with NodeOps  ) extends Approximation {
  
}