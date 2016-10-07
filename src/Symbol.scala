package collab;

trait Symbol {
  def name : String
  def toSMTLib : String
  override def toString = name
}

trait ConcreteSymbol extends Symbol {
  def args : Seq[Sort]
  def sort : Sort
}

// Should we call these polymorphic symbols?
trait TypedSymbol extends ConcreteSymbol {
  def getFactory : SymbolFactory
}

// Maybe this should extend Symbol, maybe not?
trait SymbolFactory {
  def rank : Int
  def apply(idx : Seq[Sort]) : TypedSymbol
}



