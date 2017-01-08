package uppsat.ast;

import uppsat.theory.Theory



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
  val arity : Int
  def apply(idx : Seq[BigInt]) : IndexedSort
}

trait ConstructedSortFactory {
  type Sort <: ConstructedSort
  val arity : Int
  def apply(idx : Seq[Sort]) : ConstructedSort
}
