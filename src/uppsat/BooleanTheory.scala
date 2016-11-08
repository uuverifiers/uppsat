package uppsat

object BooleanTheory extends Theory {
  val name = "BooleanTheory"
  
  
  object BooleanSort extends ConcreteSort {
      val name = "Boolean"
    }
  
  class BooleanFunctionSymbol(val name :  String, val args : Seq[Sort], val sort : Sort) extends ConcreteFunctionSymbol {   
    
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
        Some(name)
    }  
  }
  
  implicit def BoolVarToNode(boolVar : BoolVar) = LeafNode(boolVar)
  implicit def BoolFunctionToNode(boolConst : BooleanConstant) = LeafNode(boolConst)
  
  def boolAnd(left: Node, right: Node) = {
    InternalNode(BoolConjunction, List(left, right))
  }
  
  def boolNot(node: Node) = {
    InternalNode(BoolNegation, List(node))
  }
  
  // Make regular class; id is not support to be the identifier
  class BoolVar(name : String) extends BooleanConstant(name) {
  }

  val sorts = List(BooleanSort)
  val symbols = List(BoolTrue, BoolFalse, BoolConjunction, BoolDisjunction, BoolNegation)
  
  val SMTHeader = {
    "(set-info :source Boolean logic needs no theory)"
  }
  
  //TODO: Fix type-checking
  def toSMTLib(symbol : FunctionSymbol) = {
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
  
  def toSMTLib(sort : Sort) = {
    sort match {
      case BooleanSort => "Bool"
    }
  }
  
  // TODO: Fix pattern-matching
  def declarationToSMTLib(sym : FunctionSymbol) : String = {
    if (sym.isInstanceOf[BoolVar]) {
      "(declare-fun " + sym.asInstanceOf[BoolVar].name + " () " + toSMTLib(sym.asInstanceOf[BoolVar].sort) + ")"
    } else {
      "ERRRROR"
    }
  }
}