package uppsat

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
  
  
  
  // Constants   
  case object BoolTrue extends BooleanConstant("true")  
  case object BoolFalse extends BooleanConstant("false")
  
  // Symbols, conjunction and negation
  case object BoolConjunction extends BooleanBinaryFunctionSymbol("conjunction")  
  case object BoolDisjunction extends BooleanBinaryFunctionSymbol("disjunction")  
  case object BoolImplication extends BooleanBinaryFunctionSymbol("implication")  
  case object BoolNegation extends BooleanUnaryFunctionSymbol("negation")
  
  object BoolVar {
    def unapply(symbol : BoolVar) : Option[String] = {
        Some(symbol.name)
    }  
  }
  
  implicit def BoolVarToAST(boolVar : BoolVar) = Leaf(boolVar)
  implicit def BoolFunctionToAST(boolConst : BooleanConstant) = Leaf(boolConst)
  
  def boolAnd(left: AST, right: AST) = {
    AST(BoolConjunction, List(left, right))
  }
  
  def boolNot(ast: AST) = {
    AST(BoolNegation, List(ast))
  }
  
  // Make regular class; id is not support to be the identifier
  class BoolVar(name : String) extends BooleanConstant(name) {
  }

  val sorts = List(BooleanSort)
  val symbols = List(BoolTrue, BoolFalse, BoolConjunction, BoolDisjunction, BoolNegation)
  
  
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
  
  val SMTHeader = {
    "(set-info :source Boolean logic needs no theory)"
  }
  
  //TODO: Fix type-checking
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case BoolTrue => "true"
      case BoolFalse => "false"
      case BoolConjunction => "and"
      case BoolDisjunction => "or"
      // TODO: Is this correct?
      case BoolImplication => "implies"
      case BoolNegation => "not"
      case BoolVar(name) => name
    }
  }
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case BooleanSort => "Bool"
    }
  }
  
  // TODO: Fix pattern-matching
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    if (sym.isInstanceOf[BoolVar]) {
      "(declare-fun " + sym.asInstanceOf[BoolVar].name + " () " + toSMTLib(sym.asInstanceOf[BoolVar].sort) + ")"
    } else {
      "ERRRROR"
    }
  }
}