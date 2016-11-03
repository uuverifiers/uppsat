package uppsat;



// TODO: Check out what abstract means, remove?
// TODO: toSMTLib use visitor pattern insteadb
abstract trait Sort {
  def name : String
  def toSMTLib : String
  override def toString = name
}

trait ConcreteSort extends Sort {
}

trait IndexedSort extends ConcreteSort {
  def getFactory : IndexedSortFactory
}

// TODO: defs to val
trait TypedSort extends ConcreteSort {
  def getFactory : TypedSortFactory
}

// TODO: We should use BigInt instead
// TODO: Store what sort is prodcued (using generics?)
//       type Sort <: IndexedSort
trait IndexedSortFactory {
  def rank : Int
  def apply(idx : Seq[Int]) : IndexedSort
}

trait TypedSortFactory {
  def rank : Int
  def apply(idx : Seq[Sort]) : TypedSort
}
