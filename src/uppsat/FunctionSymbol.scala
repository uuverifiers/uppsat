package uppsat;

trait FunctionSymbol {
  val name : String
  val toSMTLib : String
  override def toString = name
}

trait ConcreteFunctionSymbol extends FunctionSymbol {
  val args : Seq[Sort]
  val sort : Sort
}

// TODO: Add IndexedFunctionSymbol and mimic Sort hierarchy
trait ConstructedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : ConstructedFunctionSymbolFactory
}

trait ConstructedFunctionSymbolFactory {
  val rank : Int
  def apply(idx : Seq[Sort]) : ConstructedFunctionSymbol
}

trait IndexedFunctionSymbol extends ConcreteFunctionSymbol {
  val getFactory : IndexedFunctionSymbolFactory
}

trait IndexedFunctionSymbolFactory {
  val rank : Int
  def apply(idx : Seq[Sort]) : IndexedFunctionSymbol
}






