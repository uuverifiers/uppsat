package uppsat.ast;

import uppsat.theory.Theory

/** The basic kind of sort. */
trait Sort {
  val name : String
  val theory : Theory
  override def toString = name
}

/** Conrete sorts are not indexed. */
trait ConcreteSort extends Sort {
}

/** An indexed sort is instantiated by one or more integers. */
trait IndexedSort extends ConcreteSort {
  val getFactory : IndexedSortFactory
}

/** Sort factory for indexed an indexed sort. */
trait IndexedSortFactory {
  type Sort <: IndexedSort
  val arity : Int
  def apply(idx : Seq[BigInt]) : IndexedSort
}
