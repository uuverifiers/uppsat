package uppsat.theory

import uppsat.ast._
import uppsat.theory.BooleanTheory._

object PolymorphicTheory extends Theory {
  val name = "Polymorphic"

  class PolymorphicTheoryException(msg : String)
      extends Exception("PolymorphicTheoryException: " + msg)

  class PolymorphicFunctionSymbol(val name :  String,
                                  val args : Seq[ConcreteSort],
                                  val sort : ConcreteSort)
      extends ConcreteFunctionSymbol {
    override val theory = PolymorphicTheory : Theory
  }

  class PolyITE( n :  String, typeObject : ConcreteSort)
      extends PolymorphicFunctionSymbol(n,
                                        List(BooleanSort,
                                             typeObject,
                                             typeObject),
                                        typeObject) {
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

  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)
                    (implicit translator
                         : Option[uppsat.solver.SMTTranslator] = None) = {
    symbol match {
      case pITE : PolyITE => "ite"
      case _ => {
        val msg = "Translation of undefined polymorphic symbol: " + symbol
        throw new PolymorphicTheoryException(msg)
      }
    }
  }

  def sortToSMTLib(sort : ConcreteSort)
                  (implicit translator
                       : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case _ => throw new Exception("Translating ITE sort")
    }
  }

  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String =
    throw new Exception("Requesting declaration of polymorphic symbol: " + sym)

}
