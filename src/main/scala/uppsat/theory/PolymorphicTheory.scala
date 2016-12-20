package uppsat.theory

import uppsat.theory.BooleanTheory._
import uppsat.ast._

object PolymorphicTheory extends Theory {
  val name = "Polymorphic"
  
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
  
  val SMTHeader = {
    "(set-info :source Poly logic needs no theory)"
  }
  
  //TODO: Fix pattern-matching
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    "ite"
  }
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case _ => throw new Exception("Translating ITE sort")
    }
  }
  
  // TODO: Fix pattern-matching
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    throw new Exception("Requesting declaration of ITE symbol")
  }
  
}