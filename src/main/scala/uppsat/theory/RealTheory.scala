package uppsat.theory

case class RealTheoryException(msg : String) extends Exception("Real Theory Exception: " + msg)

import uppsat.theory.BooleanTheory._
import uppsat.theory.PolymorphicTheory.PolyITE
import scala.math.BigInt.int2bigInt
import uppsat.ast._

object RealTheory extends Theory {
  val name = "RealTheory"
  
  
  object RealSort extends ConcreteSort {
      val name = "Real"
      val theory = RealTheory : Theory
    }
  
  class RealFunctionSymbol(val name :  String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends ConcreteFunctionSymbol {   
    override val theory = RealTheory
  }
  
  class RealBinaryFunctionSymbol(override val name :  String) extends RealFunctionSymbol(name, List(RealSort, RealSort), RealSort) {
  }
  
  class RealUnaryFunctionSymbol(override val name :  String) extends RealFunctionSymbol(name, List(RealSort), RealSort) {
  }
  
  class RealPredicateSymbol(override val name : String, args : Seq[ConcreteSort]) extends BooleanFunctionSymbol(name, args, BooleanSort) {
    override val theory = RealTheory
  }
  
  // TODO: Range of Reals under SMTLIB
  class RealConstant(name :  String) extends RealFunctionSymbol(name, List(), RealSort) {
  }
  
  case class RealNumeral(val value :  BigInt) extends RealConstant(value.toString()) {
  }
  
  case class RealDecimal(val value : BigDecimal) extends RealConstant(value.toString()) {
  }
  
  
  // Constants   
  val RealZero = RealNumeral(0)  
  
  
  // Symbols, conjunction and negation
  case object RealAddition extends RealBinaryFunctionSymbol("+")   
  case object RealSubstraction extends RealBinaryFunctionSymbol("-")
  case object RealNegation extends RealBinaryFunctionSymbol("negation")
  case object RealMultiplication extends RealBinaryFunctionSymbol("*")   
  case object RealDivision extends RealBinaryFunctionSymbol("/")
  case object RealEquality extends RealPredicateSymbol("=", List(RealSort, RealSort))
  case object RealLEQ extends RealPredicateSymbol("<=", List(RealSort, RealSort))
  case object RealLT extends RealPredicateSymbol("<", List(RealSort, RealSort))
  case object RealGEQ extends RealPredicateSymbol(">=", List(RealSort, RealSort))
  case object RealGT extends RealPredicateSymbol(">", List(RealSort, RealSort))
  case object RealITE extends PolyITE("ite", RealSort)
  
  implicit def NumeralToAST(int : BigInt) = Leaf(new RealNumeral(int))
  implicit def DecimalToAST(real : BigDecimal) = Leaf(new RealDecimal(real))
  
  
  implicit def RealVarToAST(RealVar : RealVar) = Leaf(RealVar)
  implicit def RealFunctionToAST(realConst : RealConstant) = Leaf(realConst)
  
  def realAddition(left: AST, right: AST) = {
    AST(RealAddition, List(left, right))
  }
  
  def realSubstraction(left: AST, right: AST) = {
    AST(RealSubstraction, List(left, right))
  }
  
  def realMultiplication(left: AST, right: AST) = {
    AST(RealMultiplication, List(left, right))
  }
  
  def realDivision(left: AST, right: AST) = {
    AST(RealDivision, List(left, right))
  }
  
  def realEquality(left: AST, right: AST) = {
    AST(RealEquality, List(left, right))
  }
  
  def realLessThanOrEqual(left: AST, right: AST) = {
    AST(RealLEQ, List(left, right))
  }
  
  def realLessThan(left: AST, right: AST) = {
    AST(RealLT, List(left, right))
  }
  
  def realGreaterThanOrEqual(left: AST, right: AST) = {
    AST(RealGEQ, List(left, right))
  }
  
  def realGreaterThan(left: AST, right: AST) = {
    AST(RealLEQ, List(left, right))
  }
  
  def parseLiteral(lit : String) = {
    val IntRegex  = """([+-]?[0-9]+)""".r
    val FracRegex = """([+-]?[0-9]+) */ *([0-9]+)""".r
    val DecRegex  = """([+-]?[0-9]*\.[0-9]*)""".r
    val DecRegexE = """([+-]?[0-9]*\.[0-9]*)[eE]([+-]?[0-9]+)""".r
    
    lit match {
      case IntRegex(i) => BigInt(i)      
      case DecRegex(i) => BigDecimal(i)
    }
  }
  
  
  object RealVar {
    def unapply(symbol : RealVar) : Option[String] = {
        Some(symbol.name)
    }  
  }
  // Make regular class; id is not support to be the identifier
  class RealVar(name : String) extends RealConstant(name) {
  }

  val sorts = List(RealSort)
  val symbols = List( RealZero,
                      RealNegation,
                      RealAddition,
                      RealSubstraction, 
                      RealMultiplication,
                      RealDivision,
                      RealLEQ,
                      RealLT,
                      RealGEQ,
                      RealGT,
                      RealEquality,
                      RealITE)
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case RealVar(_) => false
      case _ => true
    }
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case RealVar(_) => true
      case _ => false
    }
  }
  val SMTHeader = {
    "(set-logic QF_LRA)" //TODO: Check the actual logic
  }
  
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {     
      case RealAddition => "+"
      case RealSubstraction => "-"
      case RealNegation => "-"
      case RealMultiplication => "*"
      case RealDivision => "/"
      case RealEquality => "="
      case RealLEQ => "<="
      case RealGEQ => "<="
      case RealLT => "<"      
      case RealGT => ">"
      case RealNumeral(value) => value.toString()
      case RealDecimal(value) => value.toString()
      case RealVar(name) => name
      case other => throw new RealTheoryException("Unknown symbol: " + symbol)
    }
  }
  
  
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case RealSort => "Real"
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case RealVar(name) => "(declare-fun " + name + " () " + toSMTLib(sym.sort) + ")" 
      case RealNumeral(_) => ""
      case RealDecimal(_) => ""
      case _ => throw new Exception("Not instance of RealVar : " + sym.getClass)
    }
  }
}