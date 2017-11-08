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

trait ConstructedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : ConstructedFunctionSymbolFactory
}

trait ConstructedFunctionSymbolFactory {
  val arity : Int
  def apply(idx : Seq[ConcreteSort]) : ConstructedFunctionSymbol
  def apply(idx : ConcreteSort) : ConstructedFunctionSymbol = 
    apply(idx)
}

trait IndexedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : IndexedFunctionSymbolFactory
  
  def apply(sorts : ConcreteSort *) = {
      getFactory(sorts:_*)
    }
}

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






