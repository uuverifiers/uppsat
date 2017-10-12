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
  
  case class RealNumeral(val num :  BigInt, val denom : BigInt = 1) extends RealConstant(num.toString()) {
  }
  
  case class RealDecimal(val num : BigInt, val denom : BigInt) extends RealConstant("( " + num.toString() + "/" + denom.toString() + " )") {
  }
  
  
  // Constants    
  val RealOne  = RealNumeral(1)
  val RealZero = RealNumeral(0)
  
  
  // Symbols, conjunction and negation
  case object RealAddition extends RealBinaryFunctionSymbol("real-addition")   
  case object RealSubstraction extends RealBinaryFunctionSymbol("real-substraction")
  case object RealNegation extends RealBinaryFunctionSymbol("real-negation")
  case object RealMultiplication extends RealBinaryFunctionSymbol("real-multiplicatoin")   
  case object RealDivision extends RealBinaryFunctionSymbol("real-division")
  case object RealEquality extends RealPredicateSymbol("real-eq", List(RealSort, RealSort))
  case object RealLEQ extends RealPredicateSymbol("real-leq", List(RealSort, RealSort))
  case object RealLT extends RealPredicateSymbol("real-lt", List(RealSort, RealSort))
  case object RealGEQ extends RealPredicateSymbol("real-geq", List(RealSort, RealSort))
  case object RealGT extends RealPredicateSymbol("real-gt", List(RealSort, RealSort))
  case object RealITE extends PolyITE("real-ite", RealSort)
  
  implicit def NumeralToAST(int : BigInt) = Leaf(new RealNumeral(int))
  implicit def DecimalToAST(num : BigInt, denom : BigInt) = Leaf(new RealDecimal(num, denom))
  
  
  implicit def RealVarToAST(RealVar : RealVar) = Leaf(RealVar)
  implicit def RealFunctionToAST(realConst : RealConstant) = Leaf(realConst)
  
  def realAddition(left: AST, right: AST) = {
    AST(RealAddition, List(left, right))
  }
  
  def realNegate(arg : AST) = {
    AST(RealNegation, List(arg))
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
    val BIntRegex = """([0-9]+[\.0]?)""".r
    val IntRegex  = """\(?([+-]?)\s*([0-9]+[\.]?0*)\)?""".r
    val FracRegex = """([+-]?[0-9]+) */ *([0-9]+)""".r
    val DecRegex  = """([+-]?[0-9]*\.[0-9]*)""".r
    val DecRegexE = """([+-]?[0-9]*\.[0-9]*)[eE]([+-]?[0-9]+)""".r
    val enumDenom = """\(\/ ([+-]?\d+\.0) (\d+\.0)\)""".r
    
    lit match {
      case BIntRegex(num) => RealNumeral(BigDecimal(num).toBigInt())
      case IntRegex(sgn, num) =>  RealNumeral(BigDecimal(sgn + num).toBigInt())
      case enumDenom(num, denom) => RealDecimal(BigDecimal(num).toBigInt(), BigDecimal(denom).toBigInt())
      case DecRegex(i) => throw new Exception("Big decimal?" + i) //BigDecimal(i)
      case _ => throw new Exception("Failed to match _"+lit+"_")
    }
  }
  
  
  object RealVar {
    def unapply(symbol : RealVar) : Option[String] = {
        Some(symbol.name)
    }  
  }
  // Make regular class; id is not support to be the identifier
  class RealVar(_name : String) extends RealConstant(_name) {
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
    "(set-logic QF_LRA)"
  }
  
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    symbol match {     
      case RealAddition => "+"
      case RealSubstraction => "-"
      case RealNegation => "-"
      case RealMultiplication => "*"
      case RealDivision => "/"
      case RealEquality => "="
      case RealLEQ => "<="
      case RealGEQ => ">="
      case RealLT => "<"      
      case RealGT => ">"
      case RealNumeral(num, _) => num.toString()
      case RealDecimal(num, denom) => "(/ " + num + " " + denom + ")"
      case RealVar(name) => name
      case other => throw new RealTheoryException("Unknown symbol: " + symbol)
    }
  }
  
  
  
  def sortToSMTLib(sort : ConcreteSort)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case RealSort => "Real"
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case RealVar(name) => "(declare-fun " + name + " () " + sortToSMTLib(sym.sort) + ")" 
      case RealNumeral(_, _) => ""
      case RealDecimal(_, _) => ""
      case _ => throw new Exception("Not instance of RealVar : " + sym.getClass)
    }
  }
}