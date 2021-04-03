package uppsat.precision

/** Represents a precision ordering of a tuple of two integers.
  *
  * This class is used to represent precision as a tuple of two integers. This
  * is used in SmallFloats where the first integer is for exponential bits and
  * the second for significand bits. It uses an ordering of integer tuples where
  * (k, l) < (m, n) if k < m or k = m and l < n.

  */
class IntTuplePrecisionOrdering(val minimalPrecision : (Int, Int),
                                val maximalPrecision : (Int, Int))
    extends PrecisionOrdering[(Int, Int)] {

  type P = (Int, Int)
  val order = IntTupleOrdering

  /** An ordering of integer tuples.
    *
    * An ordering of integer tuples where (k, l) < (m, n) if k < m or k = m and
    * l < n.
    */
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

  def +(a : (Int, Int), b : (Int, Int)) : (Int, Int) =
    (a._1 + b._1, a._2 + b._2)
}
