package uppsat.precision


/** Represents a precision ordering of a tuple of two integers.
  *
  * This class is used to represent precision as a integer. The ordering is
  * simply regular <.
  */
class IntPrecisionOrdering(val minimalPrecision : Int,
                           val maximalPrecision : Int)
    extends PrecisionOrdering[Int] {

  type P = Int
  val order = SingleIntOrdering

  /** An ordering of integers.
    *
    * An ordering of integers, simply <.
    */
  object SingleIntOrdering extends PartialOrdering[Int] {

    def lteq(x : Int, y : Int) = x <= y

    def tryCompare(x: Int, y: Int) = {
      if (x < y)
        Some(-1)
      else if (x > y)
        Some(1)
      else
        Some(0)
    }
  }

  def +(a : Int, b : Int) : Int = a + b
}
