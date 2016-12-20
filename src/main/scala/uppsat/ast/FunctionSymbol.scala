package uppsat.ast;

import uppsat.theory.Theory

trait FunctionSymbol {
  val name : String
  val theory : Theory
  override def toString = name
}

trait ConcreteFunctionSymbol extends FunctionSymbol {
  val args : Seq[ConcreteSort]
  val sort : ConcreteSort
}

// TODO: Add IndexedFunctionSymbol and mimic Sort hierarchy
trait ConstructedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : ConstructedFunctionSymbolFactory
}

trait ConstructedFunctionSymbolFactory {
  val rank : Int
  def apply(idx : Seq[ConcreteSort]) : ConstructedFunctionSymbol
  def apply(idx : ConcreteSort) : ConstructedFunctionSymbol = 
    apply(idx)
}

trait IndexedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : IndexedFunctionSymbolFactory
}

trait IndexedFunctionSymbolFactory {
  val rank : Int
  def apply(idx : Seq[ConcreteSort]) : IndexedFunctionSymbol
}






