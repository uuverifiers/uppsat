package uppsat

import uppsat.precision.PrecisionMap
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ast.AST
import uppsat.approximation.Approximation

object Encoder {

  type PathMap = Map[Path, Path]
}

class Encoder[T](approximation : Approximation[T]) {
  def encode(ast : AST, pmap : PrecisionMap[T]) : AST = {
    approximation.encodeFormula(ast, pmap)
  }
}