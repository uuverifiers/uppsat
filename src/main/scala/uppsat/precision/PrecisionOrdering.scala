package uppsat.precision

trait PrecisionOrdering[P] {
  val order : PartialOrdering[P]
  val maximalPrecision : P
  val minimalPrecision : P
  def lt(p1 : P, p2 : P) = order.lt(p1, p2)
  def min(p1 : P, p2 : P) = if (lt(p1, p2)) p1 else p2
  def max(p1 : P, p2 : P) = if (lt(p1, p2)) p2 else p1
}