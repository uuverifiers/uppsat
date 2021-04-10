package uppsat.theory

import uppsat.ast._
import uppsat.solver.SMTTranslator

/** Empty theory used by the empty approximation. */
object EmptyTheory extends Theory {
  val name = "EmptyTheory"
  val sorts = List()
  val symbols = List()

  def parseLiteral(lit : String) = ???
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = ???
  def isVariable(symbol : ConcreteFunctionSymbol) = ???
  def SMTHeader = ""
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)
                    (implicit translator : Option[SMTTranslator] = None) = ???
  def sortToSMTLib(sort : ConcreteSort)
                  (implicit translator : Option[SMTTranslator] = None) = ???
  def declarationToSMTLib(symbol : ConcreteFunctionSymbol) = ???
}
