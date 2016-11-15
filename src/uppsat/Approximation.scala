package uppsat

trait Approximation[T] {
  val inputTheory : Theory
  val outputTheory : Theory
  def refine(precision : T) : T
}