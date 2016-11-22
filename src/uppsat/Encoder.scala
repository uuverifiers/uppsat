package uppsat

import uppsat.IntegerTheory._
import uppsat.PrecisionMap.Path

class Encoder[T](approximation : Approximation[T]) {
  def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, Map[AST, AST]) = {
    approximation.encode(ast, pmap)
  }
}