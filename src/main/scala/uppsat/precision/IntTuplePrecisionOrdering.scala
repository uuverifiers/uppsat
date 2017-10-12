package uppsat.precision

class IntTuplePrecisionOrdering(val minimalPrecision : (Int, Int), val maximalPrecision : (Int, Int)) extends PrecisionOrdering[(Int, Int)] {
  type P = (Int, Int)
  val order = IntTupleOrdering
  
  // TODO: (Aleks) Why do we need partial order?
  object IntTupleOrdering extends PartialOrdering[(Int, Int)] {
    def lteq(x : (Int, Int), y : (Int, Int)) = {
      val (x1, x2) = x
      val (y1, y2) = y
      x2 < y2 || (x2 == y2 && x1 < y1)
    }
    def tryCompare(x: (Int, Int), y: (Int, Int)) = {
      if (lteq(x, y))
        Some(-1)
      else if (lteq(y, x))
        Some(1)
      else
        Some(0)
    }
  }
  
  def +(a : (Int, Int), b : (Int, Int)) : (Int, Int) = (a._1 + b._1, a._2 + b._2)
  
}