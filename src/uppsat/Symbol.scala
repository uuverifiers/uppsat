package uppsat;
// TODO:  Symbol -> Function

trait Symbol {
  def name : String
  def toSMTLib : String
  override def toString = name
}

trait ConcreteSymbol extends Symbol {
  def args : Seq[Sort]
  def sort : Sort
}

// TODO: Add IndexedSymbol and mimic Sort hierarchy
trait TypedSymbol extends ConcreteSymbol {
  def getFactory : SymbolFactory
}

trait SymbolFactory {
  def rank : Int
  def apply(idx : Seq[Sort]) : TypedSymbol
}


// TODO: Two notions of equality, one general and one per-theory (cf, object identity and -0 = +0)



