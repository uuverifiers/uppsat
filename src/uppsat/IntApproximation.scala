package uppsat

object IntApproximation extends Approximation[Int] {
  val inputTheory = IntegerTheory
  val outputTheory = IntegerTheory
  def refine(precision : Int) = precision + 1
}