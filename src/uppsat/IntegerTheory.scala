package uppsat

object IntegerTheory extends Theory {
  val name = "IntegerTheory"
  
  
  object IntegerSort extends ConcreteSort {
      val name = "Integer"
    }
  
  class IntegerFunctionSymbol(val name :  String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends ConcreteFunctionSymbol {   
    
  }
  
  class IntegerBinaryFunctionSymbol(override val name :  String) extends IntegerFunctionSymbol(name, List(IntegerSort, IntegerSort), IntegerSort) {
  }
  
  class IntegerUnaryFunctionSymbol(override val name :  String) extends IntegerFunctionSymbol(name, List(IntegerSort), IntegerSort) {
  }
  
  // TODO: Range of integers under SMTLIB
  class IntegerConstant(name :  String) extends IntegerFunctionSymbol(name, List(), IntegerSort) {
  }
  
  case class IntLiteral(val value :  BigInt) extends IntegerConstant(value.toString()) {
  }
  
  
  // Constants   
  val IntZero = IntLiteral(0)  
  
  import uppsat.BooleanTheory._
  // Symbols, conjunction and negation
  case object IntAddition extends IntegerBinaryFunctionSymbol("addition")  
  case object IntSubstraction extends IntegerBinaryFunctionSymbol("substraction")  
  case object IntEquality extends BooleanFunctionSymbol("integer-equality", List(IntegerSort, IntegerSort), BooleanSort)
  
  
  implicit def IntToNode(int : Int) = LeafNode(new IntLiteral(int))
  implicit def IntVarToNode(intVar : IntVar) = LeafNode(intVar)
  implicit def IntFunctionToNode(intConst : IntegerConstant) = LeafNode(intConst)
  
  def intAddition(left: Node, right: Node) = {
    InternalNode(IntAddition, List(left, right))
  }
  
  def intSubstraction(left: Node, right: Node) = {
    InternalNode(IntSubstraction, List(left, right))
  }
  
  def intEquality(left: Node, right: Node) = {
    InternalNode(IntEquality, List(left, right))
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
  val symbols = List(IntZero, IntAddition, IntSubstraction)
  
  val SMTHeader = {
    "(set-logic QF_LIA)" //TODO: Check the actual logic
  }
  
  //TODO: Fix type-checking
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {     
      case IntAddition => "+"
      case IntSubstraction => "-"
      case IntEquality => "="
      case IntLiteral(value) => value.toString()
      case IntVar(name) => name
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