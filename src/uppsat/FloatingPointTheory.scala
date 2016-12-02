package uppsat

import uppsat.BooleanTheory._
import uppsat.PolymorphicTheory.PolyITE

object FloatingPointTheory extends Theory {
  val name = "FPTheory"
  
  
   object FPSortFactory extends IndexedSortFactory { 
    case class FPSort(eBits : Int, sBits : Int) extends IndexedSort {
      val name = "Floating Point (" + eBits + ", " + sBits + ")"
      val theory = FloatingPointTheory
      val getFactory = FPSortFactory
    }

    val rank = 2
    def apply(idx : Seq[BigInt]) = {
      val eBits = idx(0).toInt
      val sBits = idx(1).toInt
      // Anonymous class, notation!
      // Maybe use HashTable to store and re-use
      FPSort(eBits, sBits)
    }
  }
  
  class FPOperatorSymbolFactory(symbolName : String, isRounding : Boolean, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
    case class FPFunctionSymbol( val args : Seq[ConcreteSort], val sort : ConcreteSort) extends IndexedFunctionSymbol {   
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val name = symbolName
    }

    val rank = 1 // Refers to the sorts
    override def apply(sort : Seq[ConcreteSort]) = {
      val args = if (isRounding) RoundingModeSort :: List.fill(fpArity)(sort.head) else List.fill(fpArity)(sort.head)
      
      FPFunctionSymbol(args, sort.head)  
    }
  }
  
  import uppsat.FloatingPointTheory.FPSortFactory.FPSort
  
  object RoundingModeSort extends ConcreteSort {
    val name = "RoundingMode"
    val theory = FloatingPointTheory : Theory
  }
  
//   class FPPredicateSymbol(override val name : String, args : Seq[ConcreteSort]) extends BooleanFunctionSymbol(name, args, BooleanSort) {
//    override val theory = FloatingPointTheory
//  }
  
  // TODO: Range of floategers under SMTLIB
  
  object FPConstantFactory extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
    case class FPConstantSymbol(val name: String, val args : Seq[ConcreteSort], val sort : ConcreteSort) extends IndexedFunctionSymbol {   
      val theory = FloatingPointTheory
      val getFactory = thisFactory
    }

    val rank = 1 // Refers to the sorts
    override def apply(sort : Seq[ConcreteSort]) = {
      val args = if (isRounding) RoundingModeSort :: List.fill(fpArity)(sort.head) else List.fill(fpArity)(sort.head)
      
      FPFunctionSymbol(args, sort.head)  
    }
  }
  
  class FPLiteral(val value :  Float, sort : FPSort) extends FPConstant(value.toString(), sort) {
  }
  
  // Concrete sorts
  val FPSort_3_3 = FPSort(3,3)
  
  // Constants   
  val FPZero = FPLiteral(0, FPSort_3_3)  
  
  
  // Symbols, conjunction and negation
  case class FPAddition(sort : FPSort) extends FPBinaryRoundingFunctionSymbol("addition", sort, sort, sort)   
  case class FPSubstraction(sort : FPSort) extends FPBinaryRoundingFunctionSymbol("substraction", sort, sort, sort)  
  case class FPEquality(arg : FPSort) extends FPPredicateSymbol("fp-equality", List(arg, arg))
  case class FPLessThanOrEqual(arg : FPSort) extends FPPredicateSymbol("fp-leq", List(arg, arg))
  case class FPITE(sort : FPSort) extends PolyITE("fp-ite", sort)
  
//  implicit def FPToAST(float : Float) = Leaf(new FPLiteral(float))
//  implicit def FPVarToAST(floatVar : FPVar) = Leaf(floatVar)
//  implicit def FPFunctionToAST(floatConst : FPConstant) = Leaf(floatConst)
//  
//  def floatAddition(left: AST, right: AST) = {
//    AST(FPAddition()), List(left, right))
//  }
//  
//  def floatSubstraction(left: AST, right: AST) = {
//    AST(FPSubstraction, List(left, right))
//  }
//  
//  def floatEquality(left: AST, right: AST) = {
//    AST(FPEquality, List(left, right))
//  }
//  
//  def floatLessThanOrEqual(left: AST, right: AST) = {
//    AST(FPLessThanOrEqual, List(left, right))
//  }
  
  def parseLiteral(lit : String) = {
    //case blah blah 
    Leaf(FPLiteral(0, FPSort_3_3))
  }
  
  
  object FPVar {
    def unapply(symbol : FPVar) : Option[(String, ConcreteSort)] = {
        Some((symbol.name, symbol.sort))
    }  
  }
  // Make regular class; id is not support to be the identifier
  class FPVar(name : String, sort : FPSort) extends FPConstant(name, sort) {
  }

  val sorts = List(FPSort)
  val symbols = List(FPZero, FPAddition, FPSubstraction, FPLessThanOrEqual, FPEquality)
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FPVar(_) => false
      case _ => true
    }
  }
  
  val SMTHeader = {
    "(set-logic QF_LIA)" //TODO: Check the actual logic
  }
  
  //TODO: Fix type-checking
  def toSMTLib(symbol : ConcreteFunctionSymbol) = {
    symbol match {     
      case FPAddition(_) => "fp.add"
      case FPSubstraction(_) => "fp.sub"
      case FPEquality(_) => "="
      case FPLessThanOrEqual(_) => "<="
      case FPLiteral(value, _) => value.toString()
      case FPVar(name, _) => name
    }
  }
  
  
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case FPSort(s,e) => "(_ FP " + e + " " + s + ")" 
    }
  }
  
  // TODO: Fix floatLiteral never called
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case FPVar(name) => "(declare-fun " + name + " () " + toSMTLib(sym.sort) + ")" 
      case FPLiteral(_, _) => ""
      case _ => throw new Exception("Not instance of FPVar : " + sym.getClass)
    }
  }
}