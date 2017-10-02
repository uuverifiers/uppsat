package uppsat.theory

import uppsat.theory.BooleanTheory._
import uppsat.ast._

object PolymorphicTheory extends Theory {
  val name = "Polymorphic"

  class PolymorphicTheoryException(msg : String) extends Exception("PolymorphicTheoryException: " + msg)
  
  class PolymorphicFunctionSymbol(val name :  String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends ConcreteFunctionSymbol {
    override val theory = PolymorphicTheory : Theory
  }
  
  class PolyITE( n :  String, typeObject : ConcreteSort)
                    extends PolymorphicFunctionSymbol(n, List(BooleanSort, typeObject, typeObject), typeObject) {
  }
  
  
  val sorts = List()
  val symbols = List()

  def parseLiteral(lit : String) = 
    throw new Exception("Parsing in polymorphic theory!")
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    false
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    false
  }
  
  val SMTHeader = ""
  
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case pITE : PolyITE => "ite"
      case _ => throw new PolymorphicTheoryException("Translation of undefined polymorphic symbol: " + symbol)
    }
  }
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case _ => throw new Exception("Translating ITE sort")
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String =
    throw new Exception("Requesting declaration of polymorphic symbol: " + sym)
  
}