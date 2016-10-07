package collab;

// Check out what abstract means
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

trait TypedSort extends ConcreteSort {
  def getFactory : TypedSortFactory
}

// Maybe this should extend Sort, maybe not?
trait IndexedSortFactory {
  def rank : Int
  def apply(idx : Seq[Int]) : IndexedSort
}

trait TypedSortFactory {
  def rank : Int
  def apply(idx : Seq[Sort]) : TypedSort
}
