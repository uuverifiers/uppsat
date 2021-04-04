package uppsat.theory

import uppsat.ast._
import uppsat.solver.SMTTranslator

trait Theory {
  val name : String
  val sorts : Seq[Sort]
  val symbols : Seq[FunctionSymbol]

  def parseLiteral(lit : String) : AST
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) : Boolean
  def isVariable(symbol : ConcreteFunctionSymbol) : Boolean
  def SMTHeader : String
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)
                    (implicit translator : Option[SMTTranslator] = None)
      : String
  def sortToSMTLib(sort : ConcreteSort)
                  (implicit translator : Option[SMTTranslator] = None) : String
  def declarationToSMTLib(symbol : ConcreteFunctionSymbol) : String
}
