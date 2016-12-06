package uppsat.theory

import uppsat.theory.BooleanTheory._
import scala.math.BigInt.int2bigInt
import uppsat.ast._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort

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
  
  abstract class FloatingPointFunctionSymbol(val sort : FPSort) extends IndexedFunctionSymbol
  abstract class FloatingPointConstantSymbol(override val sort : FPSort) extends FloatingPointFunctionSymbol(sort)
  abstract class FloatingPointPredicateSymbol extends IndexedFunctionSymbol
  
  case class FPOperatorSymbolFactory(symbolName : String, isRounding : Boolean, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
    case class FPFunctionSymbol(val args : Seq[ConcreteSort], override val sort : FPSort) extends FloatingPointFunctionSymbol(sort) {   
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val name = symbolName
    }
    
    val rank = 1 // Refers to the sorts
    override def apply(sorts : Seq[ConcreteSort]) = {
      sorts.reverse.head match {
        case fpsort : FPSort => {      
          val argSorts = sorts.take(sorts.length - 1).toList
          val args = if (isRounding) RoundingModeSort :: argSorts else argSorts
          FPFunctionSymbol(args, fpsort)
        }
        case _ =>  throw new Exception("Non-FP sort : " + sorts.head)
      }  
    }
  }

  case class FPPredicateSymbolFactory(symbolName : String, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPPredicateSymbol( val argSort : ConcreteSort) extends FloatingPointPredicateSymbol {   
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
  
  
  object RoundingModeSort extends ConcreteSort {
    val name = "RoundingMode"
    val theory = FloatingPointTheory : Theory
  }
    
  abstract class RoundingMode extends ConcreteFunctionSymbol
  
  object RoundToZero extends RoundingMode {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToZero"
  }

  object RoundToPositive extends RoundingMode {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToPositive"
  }
  
  
  case class FPConstantFactory(sign : Int, eBits: List[Int], sBits : List[Int]) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPConstantSymbol(override val sort : FPSort) extends FloatingPointConstantSymbol(sort) {
      // TODO: Does name have to be SMT-appliant, not nice!
      val name = fpToFloat(sign, eBits, sBits).toString() 
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val args = List()
    }

    val rank = 1 // Refers to the sorts

    override def apply(sort : Seq[ConcreteSort]) = {
      sort.head match {
        case fpsort : FPSort => {          
          FPConstantSymbol(fpsort)
        }
        case _ =>  throw new Exception("Non-FP sort : " + sort.head)
      }  
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
  val FPToFPFactory = new FPOperatorSymbolFactory("fp-to-fp", true, 1)
  // case class FPITE(sort : FPSort) extends PolyITE("fp-ite", sort)
  
  
  // Interface
  def fp(sign : Int, eBits : List[Int], sBits : List[Int])(implicit sort : FPSort) = {
    val factory = new FPConstantFactory(sign, eBits, sBits)
    factory(List(sort))
  } 
  
  def intToBits(int : Int, upperBound : Int) = {
    (for ( i <- 0 until upperBound) yield {
      if ((int & (1 << i )) > 0) 1 else 0
    }).reverse.toList
  }
  
  def floatToBits(f : Float) = {
    val bits = java.lang.Float.floatToIntBits(f)
    val bitList = intToBits(bits,32)
    val sign  = bitList.head //intToBits(bits & 0x80000000, 1)
    val ebits = bitList.tail.take(8)//intToBits(bits & 0x7f800000, 8)
    val sbits = bitList.drop(9)//intToBits(bits & 0x007fffff, 23)
    (sign, ebits, sbits)
  }
  
  implicit def floatToAST(float : Float) = {
    val sort = FPSortFactory(List(8,24))
    val (sign, ebits, sbits) = floatToBits(float)
    Leaf(fp(sign, ebits, sbits)(sort))    
  }
  
  implicit def FPVarToAST(floatVar : FPVar) = Leaf(floatVar)
  implicit def RoundingModeToAST(rm : RoundingMode) = Leaf(rm)

  
  def genericOperation(left : AST, right : AST, rm : RoundingMode, factory : FPOperatorSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FPSort, r : FPSort) => {
        if (l != r)
          throw new Exception("FP-Operation of non-equal sorts!")
        val children : List[AST] = List(rm, left, right)
        AST(factory(List(l, l, l)), children)
      }
      case _ => throw new Exception("FP-Opreation of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def floatAddition(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPAdditionFactory)

  def floatSubtraction(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPAdditionFactory)
    
  def genericPredicate(left : AST, right : AST, factory : FPPredicateSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FPSort, r : FPSort) => {
        if (l != r)
          throw new Exception("FP-Predicate of non-equal sorts!")
        val children : List[AST] = List(left, right)
        val fpeq = factory(List(l))
        AST(fpeq, children)
      }
      case _ => throw new Exception("FP-Predicate of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def floatEquality(left : AST, right : AST) = 
    genericPredicate(left, right, FPEqualityFactory)

  def floatLessThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, FPLessThanOrEqualFactory)
   
    
  // TODO: How to do this translation?
  def bitsToInt(bits : List[Int]) : Int = {
    def bti(bs : List[Int], exp : Int, ack : Int) : Int = {
      bs match {
        case Nil => ack
        case 0 :: tail => bti(tail, exp*2, ack)
        case 1 :: tail => bti(tail, exp*2, ack+exp)
        case _ => throw new Exception("List contains non-binary digit: " + bs)
      }
    }
    bti(bits.reverse, 1, 0)
  }
  
  def sbitsToFloat(bits : List[Int]) : Float = {
    def bti(bs : List[Int], exp : Float, ack : Float) : Float = {
      bs match {
        case Nil => ack
        case 0 :: tail => bti(tail, exp/2, ack)
        case 1 :: tail => bti(tail, exp/2, ack+exp)
        case _ => throw new Exception("List contains non-binary digit: " + bs)
      }
    }
    bti(bits, 0.5f, 0)
  }
  
  def ebitsToInt(bits : List[Int]) : Int = {
    val sum = bitsToInt(bits.tail.reverse)
    if (bits.head == 0) {
      sum - 2.pow(bits.length - 1).toInt
    } else {
      sum
    }        
   }
  
  def fpToFloat(signBit : Int, eBits : List[Int], sBits : List[Int]) = {
    val sign = (signBit == 0)
    val exponent = 2.pow(eBits.length - 1).toInt - 1 - bitsToInt(eBits)
    val significand = sbitsToFloat(sBits)
    val magnitude = if (exponent >= 0) (2.pow(exponent).toInt) else (1.0 / (2.pow(-exponent).toInt))
    // If denormal, etc
    val absVal = (1 + significand) * magnitude
    if (sign) absVal else -absVal    
  }
  
  def parseLiteral(lit : String) = {
    val bitPattern = "\\(fp #b(\\d+) #b(\\d+) #b(\\d+)\\)".r
    val specialPattern = "\\(_ ([a-z\\-]*) (\\d+) (\\d+)\\)".r
    val testPattern = "\\(_ ([a-z\\-]*)(.*)".r
    lit match {
      case bitPattern(d1, d2, d3) => {
        val constFactory = new FPConstantFactory(d1.toInt, d2.toList.map(_.toString.toInt), d3.toList.map(_.toString.toInt))
        val fpsort = FPSortFactory(List(d2.length, d3.length))
        Leaf(constFactory(List(fpsort)))
      }
      case specialPattern(d1, d2, d3) => {
        val fpsort = FPSortFactory(List(d2.toInt, d3.toInt - 1))
        val constFactory =
          d1 match {
            case "-zero" => new FPConstantFactory(1, List.fill(d2.toInt)(0), List.fill(d3.toInt - 1)(0))
            case _ => throw new Exception("Couldn't match special FP type: " + d1 + " in (" + lit + ")")
          }
          Leaf(constFactory(List(fpsort)))
      }
      case _ => {
        throw new Exception("fp.parseLiteral error: " + lit)
      }
    }
  }
  
  
  object FPVar {
    def apply(name : String)(implicit sort : FPSort) = {
      new FPVar(name, sort)
    }
    
    def unapply(symbol : FPVar) : Option[(String, ConcreteSort)] = {
        Some((symbol.name, symbol.sort))
    }  
  }
  
  class FPVar(val name : String, val sort : FPSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = FloatingPointTheory
  }

  // TODO: What to do with this
  val sorts : List[Sort] = List()

  // TODO: How do we do this?
  val symbols = List() //: List[IndexedFunctionSymbol] = List(FPAdditionFactory.FPFunctionSymbol, FPSubtractionFactory.FPFunctionSymbol, FPEqualityFactory.FPPredicateSymbol)
  
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
      case RoundToPositive => "RTP"
      case fpFunSym : FloatingPointFunctionSymbol => {      
        fpFunSym.getFactory match {
          case FPAdditionFactory => "fp.add"
          case FPSubtractionFactory => "fp.sub"
          case FPToFPFactory => "(_ to_fp " + fpFunSym.sort.eBits + " " + fpFunSym.sort.sBits + ")"          
          case FPConstantFactory(sign, eBits, sBits) => {
            "(fp #b" + sign + " #b" + eBits.mkString("") + " #b" + sBits.mkString("") + ")" 
          }
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
      case fpPredSym : FloatingPointPredicateSymbol => {
        fpPredSym.getFactory match {
          case FPEqualityFactory => "="
          case FPLessThanOrEqualFactory => "fp.leq"
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      
      }
    }
  }
  
  
  
  def toSMTLib(sort : ConcreteSort) = {
    sort match {
      case FPSort(e, s) => "(_ FloatingPoint " + e + " " + s + ")"
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