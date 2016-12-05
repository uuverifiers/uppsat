package uppsat

import uppsat.BooleanTheory._
import uppsat.PolymorphicTheory.PolyITE
import java.math.RoundingMode

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
      // TODO: Use HashTable to store and re-use
      FPSort(eBits, sBits)
    }
  }
  
  case class FPOperatorSymbolFactory(symbolName : String, isRounding : Boolean, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
    case class FPFunctionSymbol(val args : Seq[ConcreteSort], val sort : ConcreteSort) extends IndexedFunctionSymbol {   
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

  case class FPPredicateSymbolFactory(symbolName : String, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPPredicateSymbol( val argSort : ConcreteSort) extends IndexedFunctionSymbol {   
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val name = symbolName
      val sort = BooleanSort
      val args = List.fill(fpArity)(argSort)
    }

    val rank = 1 // Refers to the sorts
    override def apply(sort : Seq[ConcreteSort]) = {      
      FPPredicateSymbol(sort.head)  
    }
  }
  
  
  import uppsat.FloatingPointTheory.FPSortFactory.FPSort
  
  object RoundingModeSort extends ConcreteSort {
    val name = "RoundingMode"
    val theory = FloatingPointTheory : Theory
  }
  
  object RoundToZero extends ConcreteFunctionSymbol {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToZero"
  }
  
  case class FPConstantFactory(sign : Int, eBits : List[Int], sBits : List[Int]) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPConstantSymbol(val sort : ConcreteSort) extends IndexedFunctionSymbol {
      // TODO: Does name have to be SMT-appliant, not nice!
      val name = fpToFloat(sign, eBits, sBits).toString() 
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val args = List()
    }

    val rank = 1 // Refers to the sorts

    override def apply(sort : Seq[ConcreteSort]) = {
      FPConstantSymbol(sort.head)
    }
  }
  
  // TODO: Change to Booleans?
  def FPLiteral(sign : Int, eBits : List[Int], sBits : List[Int], sort : FPSort) = {
    val newFactory = new FPConstantFactory(sign, eBits, sBits)
    newFactory(List(sort))
  }
  
  // Concrete sorts
  val FPSort_3_3 = FPSortFactory(List(3, 3))
  
  // Constants, signed zeroes, NaN, infinities
  val FPZero = {
    val zeroFactory = new FPConstantFactory(0, List(0, 0, 0), List(0, 0))
    zeroFactory(List(FPSort_3_3))
  }
    
  // Symbols, conjunction and negation

  val FPAdditionFactory = new FPOperatorSymbolFactory("addition", true, 2)
  val FPSubtractionFactory = new FPOperatorSymbolFactory("subtraction", true, 2)
  val FPEqualityFactory = new FPPredicateSymbolFactory("fp-equality", 2)
  val FPLessThanOrEqualFactory = new FPPredicateSymbolFactory("fp-leq", 2)  
  // case class FPITE(sort : FPSort) extends PolyITE("fp-ite", sort)
  
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
  
  def bitsToInt(bits : List[Int]) : Int = {
    def bti(bs : List[Int], exp : Int, ack : Int) : Int = {
      bs match {
        case Nil => ack
        case 0 :: tail => bti(tail, exp*2, ack)
        case 1 :: tail => bti(tail, exp*2, ack+exp)
      }
    }
    bti(bits.reverse, 1, 0)
  }
  
  def fpToFloat(signBit : Int, eBits : List[Int], sBits : List[Int]) = {
    val sign = (signBit == 0)
    val exponent = bitsToInt(eBits)
    val significand = bitsToInt(sBits)
    val absVal = (1 + significand) * (2^exponent)
    val value = if (sign) absVal else -absVal
    value
  }
  
  def parseLiteral(lit : String) = {
    val pattern = "\\(fp #b(\\d+) #b(\\d+) #b(\\d+)\\)".r
    val pattern(d1, d2, d3) = lit
    val constFactory = new FPConstantFactory(d1.toInt, d2.toList.map(_.toString.toInt), d3.toList.map(_.toString.toInt))
    val fpsort = FPSortFactory(List(d2.length, d3.length+1))
    val newConst = constFactory(List(fpsort))
    Leaf(newConst)
  }
  
  
  object FPVar {
    def unapply(symbol : FPVar) : Option[(String, ConcreteSort)] = {
        Some((symbol.name, symbol.sort))
    }  
  }
  // Make regular class; id is not support to be the identifier
  class FPVar(val name : String, val sort : FPSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = FloatingPointTheory
  }

  // TODO: What to do with this
  val sorts : List[Sort] = List()

  // TODO: How do we do this?
  val symbols = List()
  
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FPVar(_) => false
      case _ => true
    }
  }
  
  val SMTHeader = {
    "(set-logic QF_FP)" //TODO: Check the actual logic
  }
  
  //TODO: Fix type-checking
  def toSMTLib(symbol : ConcreteFunctionSymbol) = { 
    symbol match {
      case FPVar(name, _) => name
      case RoundToZero => "RTZ"
      case idxSym : IndexedFunctionSymbol => {      
        idxSym.getFactory match {
          case FPAdditionFactory => "fp.add"
          case FPSubtractionFactory => "fp.sub" 
          case FPEqualityFactory => "="
          case FPConstantFactory(sign, eBits, sBits) => "(fp #b" + sign + " #b" + eBits.mkString("") + " #b" + sBits.mkString("") + ")" 
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
    }
  }
  
  
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case FPSort(s,e) => "(_ FloatingPoint " + e + " " + s + ")"
      case RoundingModeSort => "RoundingMode"
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case FPVar(name) => "(declare-fun " + name + " () " + toSMTLib(sym.sort) + ")"
      case _ => throw new Exception("Not instance of FPVar : " + sym.getClass)
    }
  }
}