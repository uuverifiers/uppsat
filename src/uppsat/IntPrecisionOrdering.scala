package uppsat

class IntPrecisionOrdering(val max : Int) extends PrecisionOrdering[Int] {
  type P = Int
  val order = SingleIntOrdering
  
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
}