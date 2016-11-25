package uppsat

import uppsat.IntegerTheory._
import uppsat.PrecisionMap.Path
import uppsat.Encoder.PathMap

object Encoder {
  import uppsat.PrecisionMap.Path
  type PathMap = Map[Path, Path]
}

class Encoder[T](approximation : Approximation[T]) {
  def encode(ast : AST, pmap : PrecisionMap[T]) : (AST, PathMap) = {
    approximation.encode(ast, pmap)
  }
}