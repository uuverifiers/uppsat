package uppsat.ast;

import uppsat.theory.Theory

/** A function symbol. */
trait FunctionSymbol {
  val name : String
  val theory : Theory
  override def toString = name
}

/** A concrete function symbol, i.e., not indexed. */
trait ConcreteFunctionSymbol extends FunctionSymbol {
  val args : Seq[ConcreteSort]
  val sort : ConcreteSort
}

/** An indexed function symbol is instantiated by one or more integers. */
trait IndexedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : IndexedFunctionSymbolFactory

  def apply(sorts : ConcreteSort *) = {
      getFactory(sorts:_*)
    }
}

/** Factory for an indexed function symbol */
trait IndexedFunctionSymbolFactory {
  val arity : Int
  def apply(idx : ConcreteSort*) : IndexedFunctionSymbol
  def unapply(f : ConcreteFunctionSymbol) : Option[IndexedFunctionSymbol] = {
    f match {
      case f : IndexedFunctionSymbol if f.getFactory == this => Some(f)
      case _ => None
    }
  }
}
