package uppsat;



trait Sort {
  val name : String
  val theory : Theory
  override def toString = name
}

trait ConcreteSort extends Sort {
}

trait IndexedSort extends ConcreteSort {
  val getFactory : IndexedSortFactory
}

trait ConstructedSort extends ConcreteSort {
  val getFactory : ConstructedSortFactory
}

trait IndexedSortFactory {
  type Sort <: IndexedSort
  val rank : Int
  def apply(idx : Seq[BigInt]) : IndexedSort
}

trait ConstructedSortFactory {
  type Sort <: ConstructedSort
  val rank : Int
  def apply(idx : Seq[Sort]) : ConstructedSort
}
