package uppsat.theory

case class IntegerTheoryException(msg : String) extends Exception("Integer Theory Exception: " + msg)

import uppsat.theory.BooleanTheory._
import uppsat.theory.PolymorphicTheory.PolyITE
import scala.math.BigInt.int2bigInt
import uppsat.ast._

object IntegerTheory extends Theory {
  val name = "IntegerTheory"
  
  
  object IntegerSort extends ConcreteSort {
      val name = "Integer"
      val theory = IntegerTheory : Theory
    }
  
  class IntegerFunctionSymbol(val name :  String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends ConcreteFunctionSymbol {   
    override val theory = IntegerTheory
  }
  
  class IntegerBinaryFunctionSymbol(override val name :  String) extends IntegerFunctionSymbol(name, List(IntegerSort, IntegerSort), IntegerSort) {
  }
  
  class IntegerUnaryFunctionSymbol(override val name :  String) extends IntegerFunctionSymbol(name, List(IntegerSort), IntegerSort) {
  }
  
  class IntegerPredicateSymbol(override val name : String, args : Seq[ConcreteSort]) extends BooleanFunctionSymbol(name, args, BooleanSort) {
    override val theory = IntegerTheory
  }
  
  // TODO: Range of integers under SMTLIB
  class IntegerConstant(name :  String) extends IntegerFunctionSymbol(name, List(), IntegerSort) {
  }
  
  case class IntLiteral(val value :  BigInt) extends IntegerConstant(value.toString()) {
  }
  
  
  // Constants   
  val IntZero = IntLiteral(0)  
  
  
  // Symbols, conjunction and negation
  case object IntAddition extends IntegerBinaryFunctionSymbol("addition")   
  case object IntSubstraction extends IntegerBinaryFunctionSymbol("substraction")  
  case object IntEquality extends IntegerPredicateSymbol("integer-equality", List(IntegerSort, IntegerSort))
  case object IntLessThanOrEqual extends IntegerPredicateSymbol("integer-leq", List(IntegerSort, IntegerSort))
  case object IntITE extends PolyITE("integer-ite", IntegerSort)
  
  implicit def IntToAST(int : Int) = Leaf(new IntLiteral(int))
  implicit def IntVarToAST(intVar : IntVar) = Leaf(intVar)
  implicit def IntFunctionToAST(intConst : IntegerConstant) = Leaf(intConst)
  
  def intAddition(left: AST, right: AST) = {
    AST(IntAddition, List(left, right))
  }
  
  def intSubstraction(left: AST, right: AST) = {
    AST(IntSubstraction, List(left, right))
  }
  
  def intEquality(left: AST, right: AST) = {
    AST(IntEquality, List(left, right))
  }
  
  def intLessThanOrEqual(left: AST, right: AST) = {
    AST(IntLessThanOrEqual, List(left, right))
  }
  
  def parseLiteral(lit : String) = {
    val negPattern = "\\(- (\\d+)\\)".r
    val posPattern = "(\\d+)".r
    lit match {
      case negPattern(i) => -(i.toInt)
      case posPattern(i) => i.toInt
    }
  }
  
  
  object IntVar {
    def unapply(symbol : IntVar) : Option[String] = {
        Some(symbol.name)
    }  
  }
  // Make regular class; id is not support to be the identifier
  class IntVar(name : String) extends IntegerConstant(name) {
  }

  val sorts = List(IntegerSort)
  val symbols = List(IntZero, IntAddition, IntSubstraction, IntLessThanOrEqual, IntEquality)
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case IntVar(_) => false
      case _ => true
    }
  }
  
  val SMTHeader = {
    "(set-logic QF_LIA)" //TODO: Check the actual logic
  }
  
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {     
      case IntAddition => "+"
      case IntSubstraction => "-"
      case IntEquality => "="
      case IntLessThanOrEqual => "<="
      case IntLiteral(value) => value.toString()
      case IntVar(name) => name
      case other => throw new IntegerTheoryException("Unknown symbol: " + symbol)
    }
  }
  
  
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case IntegerSort => "Int"
    }
  }
  
  // TODO: Fix intLiteral never called
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case IntVar(name) => "(declare-fun " + name + " () " + toSMTLib(sym.sort) + ")" 
      case IntLiteral(_) => ""
      case _ => throw new Exception("Not instance of IntVar : " + sym.getClass)
    }
  }
}