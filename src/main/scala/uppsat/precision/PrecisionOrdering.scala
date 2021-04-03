package uppsat.precision

/** A precision ordering.
    *
    * A precision ordering needs to have defined an ordering, a maximum, minimum
    * and addition operator.
  */
trait PrecisionOrdering[P] {
  /** The ordering of the underlying precision type */
  val order : PartialOrdering[P]

  /** Maximal possible precision of this ordering */
  val maximalPrecision : P

  /** Minimal possible precision of this ordering */
  val minimalPrecision : P

  /** Checks is {@code p1} is less than {@code p2}
    *
    * @param p1 First precision
    * @param p2 Second precision
    */
  def lt(p1 : P, p2 : P) = order.lt(p1, p2)

  /** Gives the minimum of {@code p1} and {@code p2}.
    *
    * @param p1 First precision
    * @param p2 Second precision
    */
  def min(p1 : P, p2 : P) = if (lt(p1, p2)) p1 else p2

  /** Gives the maximum of {@code p1} and {@code p2}.
    *
    * @param p1 First precision
    * @param p2 Second precision
    */
  def max(p1 : P, p2 : P) = if (lt(p1, p2)) p2 else p1

  // TODO (ptr): Do we really need addition of precisions?
  /** Adding two precisions together.
    */
  def +(p1 : P, p2 : P) : P
}
