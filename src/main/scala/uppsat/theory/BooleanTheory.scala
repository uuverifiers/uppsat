package uppsat.theory

import uppsat.ast._

case class BooleanTheoryException(msg : String) extends Exception("Boolean Theory Exception: " + msg)

object BooleanTheory extends Theory {
  val name = "BooleanTheory"
  
  
  object BooleanSort extends ConcreteSort {
      val name = "Boolean"
      val theory = BooleanTheory : Theory
    }
  
  class BooleanFunctionSymbol(val name :  String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends ConcreteFunctionSymbol {
    override val theory = BooleanTheory : Theory
  }
  
  class BooleanBinaryFunctionSymbol(override val name :  String) extends BooleanFunctionSymbol(name, List(BooleanSort, BooleanSort), BooleanSort) {
  }
  
  class BooleanUnaryFunctionSymbol(override val name :  String) extends BooleanFunctionSymbol(name, List(BooleanSort), BooleanSort) {
  }
  
  class BooleanConstant(override val name :  String) extends BooleanFunctionSymbol(name, List(), BooleanSort) {
  }
  
  

  case class NaryConjunction(argCount : Int) extends BooleanFunctionSymbol("nary-conjunction", List.fill(argCount)(BooleanSort), BooleanSort)
  def naryConjunction(i : Int) = new NaryConjunction(i)
  
  case class NaryDisjunction(argCount : Int) extends BooleanFunctionSymbol("nary-disjunction", List.fill(argCount)(BooleanSort), BooleanSort)
  def naryDisjunction(i : Int) = new NaryDisjunction(i)  
 
 
  // Constants   
  case object BoolTrue extends BooleanConstant("true")  
  case object BoolFalse extends BooleanConstant("false")
  
  // Symbols, conjunction and negation
  case object BoolConjunction extends BooleanBinaryFunctionSymbol("conjunction")
  case object BoolDisjunction extends BooleanBinaryFunctionSymbol("disjunction")  
  case object BoolExclusiveDisjunction extends BooleanBinaryFunctionSymbol("exclusive-disjunction")  
  case object BoolImplication extends BooleanBinaryFunctionSymbol("implication")
  case object BoolEquality extends BooleanBinaryFunctionSymbol("equality")
  case object BoolNegation extends BooleanUnaryFunctionSymbol("negation")
  
  
  implicit def BoolVarToAST(boolVar : BoolVar) = Leaf(boolVar)
  implicit def BoolFunctionToAST(boolConst : BooleanConstant) = Leaf(boolConst)
  
  def boolAnd(left: AST, right: AST) = {
    AST(BoolConjunction, List(left, right))
  }
  
  def boolNaryAnd(asts : List[AST]) = {
    AST(naryConjunction(asts.length), asts)
  }
  
  def boolNaryOr(asts : List[AST]) = {
    AST(naryDisjunction(asts.length), asts)
  }
  
  def boolNot(ast: AST) = {
    AST(BoolNegation, List(ast))
  }
  
  def boolEquality(left : AST, right : AST) = {
    AST(BoolEquality, List(left, right))
  }
  
  // Make regular class; id is not support to be the identifier
  // TODO: (Philipp) Can't we use case class? Please?
  case class BoolVar(val name : String) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = BooleanTheory
    val sort = BooleanSort
  }

  val sorts = List(BooleanSort)
  val symbols = List(BoolTrue, BoolFalse, BoolConjunction, BoolDisjunction, BoolExclusiveDisjunction, BoolNegation)
  
  
  def parseLiteral(lit : String) = {
    lit match {
      case "true" => BoolTrue
      case "false" => BoolFalse
      case _ => throw new Exception("Couldn't parse (Boolean) literal: " + lit)
    }
  }
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case BoolVar(_) => false
      case _ => true
    }
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case BoolVar(_) => true
      case _ => false
    }
  }
  
  val SMTHeader = ""
  
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    symbol match {
      case BoolTrue => "true"
      case BoolFalse => "false"
      case BoolConjunction => "and"
      case nc : NaryConjunction => "and"
      case nd : NaryDisjunction => "or"
      case BoolDisjunction => "or"
      case BoolExclusiveDisjunction=> "xor"
      case BoolEquality => "="
      case BoolImplication => "=>"
      case BoolNegation => "not"
      case BoolVar(name) => name
      case bc : BooleanConstant => bc.name 
      case _ => throw new BooleanTheoryException("Boolean translation of non-Boolean symbol: " + symbol)
    }
  }
  
  override def sortToSMTLib(sort : ConcreteSort)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case BooleanSort => "Bool"
      case _ => throw new BooleanTheoryException("Boolean translation of non-Boolean sort: " + sort)
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case BoolVar(name) => "(declare-fun " + name + " () " + sortToSMTLib(BooleanSort) + ")"
      case _ => throw new BooleanTheoryException("Boolean Declaration of non-Boolean symbol: " + sym)      
    }
  }
}