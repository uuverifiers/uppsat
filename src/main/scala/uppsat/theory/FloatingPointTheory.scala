package uppsat.theory

import uppsat.theory.BooleanTheory._
import scala.math.BigInt.int2bigInt
import uppsat.ast._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import scala.collection.mutable.WrappedArray

case class FloatingPointTheoryException(msg : String) extends Exception("Floating Point Theory Exception: " + msg)

object FloatingPointTheory extends Theory {
  val name = "FPTheory"
    
  object FPSortFactory extends IndexedSortFactory { 
    case class FPSort(eBitWidth : Int, sBitWidth : Int) extends IndexedSort {
      val name = "Floating Point (" + eBitWidth + ", " + sBitWidth + ")"
      val theory = FloatingPointTheory
      val getFactory = FPSortFactory
    }
  
    val arity = 2 
    def apply(idx : Seq[BigInt]) = {
      val eBits = idx(0).toInt
      val sBits = idx(1).toInt
      // TODO: Use HashTable to store and re-use
      FPSort(eBits, sBits)
    }
  }
  
  abstract class FloatingPointSymbol extends IndexedFunctionSymbol
  abstract class FloatingPointFunctionSymbol(val sort : FPSort) extends FloatingPointSymbol
  abstract class FloatingPointPredicateSymbol extends FloatingPointSymbol
  abstract class FloatingPointNonFPSymbol(val sort : ConcreteSort) extends FloatingPointSymbol
  abstract class FloatingPointConstantSymbol(override val sort : FPSort) extends FloatingPointFunctionSymbol(sort)
  

  abstract class FPGenConstantFactory extends IndexedFunctionSymbolFactory {
    def getName(sort : FPSort) : String
  }

  object FloatingPointLiteral {
    def apply(sign : Int, eBits : List[Int], sBits : List[Int], sort : FPSort) : FloatingPointLiteral = {
      if (!eBits.contains(1) && !sBits.contains(1))
        throw new FloatingPointTheoryException("Trying to create 0 with ConstantFactory")
      val newFactory = new FPConstantFactory(sign, eBits, sBits)
      if (sort.eBitWidth != eBits.length || sort.sBitWidth != sBits.length + 1) {
        throw new Exception("Creating literal with wrong sort? " + sort + ", " + eBits + ", " + sBits)
      }
      newFactory(sort).asInstanceOf[FloatingPointLiteral]
    }
  }

  case class FloatingPointLiteral(_sort : FPSort, getFactory : FPGenConstantFactory)
             extends FloatingPointConstantSymbol(_sort) {
    val name = getFactory getName sort
    val theory = FloatingPointTheory
    val args = List()
    lazy val sign = getFactory.asInstanceOf[FPConstantFactory].sign
    lazy val eBits = getFactory.asInstanceOf[FPConstantFactory].eBits take sort.eBitWidth
    lazy val sBits = getFactory.asInstanceOf[FPConstantFactory].sBits take (sort.sBitWidth - 1)
  }
  
  case class FPFunctionSymbol(val args : Seq[ConcreteSort], _sort : FPSort, val getFactory : FPFunctionSymbolFactory) 
             extends FloatingPointFunctionSymbol(_sort) {   
    val theory = FloatingPointTheory
    val name = getFactory.symbolName
  }
  
  case class FPPredicateSymbol( val argSort : ConcreteSort, val getFactory : FPPredicateSymbolFactory) extends FloatingPointPredicateSymbol {   
    val theory = FloatingPointTheory    
    val name = getFactory symbolName
    val sort = BooleanSort
    val args = List.fill(getFactory fpArity)(argSort)
  }
  case class FPToNonFPFunctionSymbol( val args : Seq[ConcreteSort], _sort : ConcreteSort, val getFactory : FPToNonFPFunctionSymbolFactory) extends FloatingPointNonFPSymbol(_sort) {
    val theory = FloatingPointTheory
    val name = getFactory symbolName
    
    
  }
  
  case class FPFunctionSymbolFactory(symbolName : String, isRounding : Boolean, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    val arity = 1 // Refers to the sorts
    def apply(sorts : ConcreteSort*) = {
      sorts.reverse.head match {
        case fpsort : FPSort => {      
          val argSorts = sorts.take(sorts.length - 1).toList
          val args = if (isRounding) RoundingModeSort :: argSorts else argSorts
          FPFunctionSymbol(args, fpsort, this)
        }
        case _ =>  throw new Exception("Non-FP sort : " + sorts.head)
      }  
    }
  }
  
  case class FPVarFactory(varName : String) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    val arity = 0
    
    def apply(sort : ConcreteSort*) = {
      sort match {
        case List(fpsort : FPSort) => 
          FPVar(varName, fpsort)        
        case _ =>  throw new Exception("Non-FP sort : " + sorts.head)
      }  
    }
  }
  
  case class FPPredicateSymbolFactory(symbolName : String, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {      
      FPPredicateSymbol(sort.head, this)  
    }
  }

  // TODO: Bitset instead of List[Int]
  case class FPConstantFactory(sign : Int, eBits: List[Int], sBits : List[Int]) extends FPGenConstantFactory {
    val thisFactory = this

    def getName(sort : FPSort) = {
      sign + " " +
      eBits.take(sort.eBitWidth).mkString("") + " " +
      sBits.take(sort.sBitWidth - 1).mkString("")
    }
    
    val arity = 1 // Refers to the sorts
    
    override def apply(sort : ConcreteSort*) = {
      sort.head match {
        case fpsort : FPSort =>
          FloatingPointLiteral(fpsort, this)
        case _ =>  throw new Exception("Non-FP sort : " + sort.head)
      }  
    }    
  }

  case class FPToNonFPFunctionSymbolFactory(symbolName : String, isRounding : Boolean, sort : ConcreteSort) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    val arity = 1 // Refers to the sorts
    def apply(argSorts : ConcreteSort*) = { //TODO : Should be FPSort, but this does not seem enforceable atm
      val args = if (isRounding) RoundingModeSort :: argSorts.toList else argSorts
      FPToNonFPFunctionSymbol(args, sort, this)
    }
  }
case class FPSpecialValuesFactory(symbolName : String) extends FPGenConstantFactory {
    val thisFactory = this

    def getName(sort : FPSort) = symbolName
    
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {
      // TODO: (Peter) Maybe we can avoid the sort.toList here
      sort.toList match {
        case List(fpsort : FPSort) => {      
          FloatingPointLiteral(fpsort, this)
        }
        case _ =>  throw new Exception("Non-FP singleton sort in special values  : " + sort.head)
      }  
    }
  }

  
  /////////////////////////////////////////////  
  // SMT-LIB SUPPORTED SYMBOLS
  /////////////////////////////////////////////
  
  
  // SORTS 
  object RoundingModeSort extends ConcreteSort {
    val name = "RoundingMode"
    val theory = FloatingPointTheory : Theory
  } 
  
  abstract class RoundingMode extends ConcreteFunctionSymbol
  
  case object RoundingModeEquality extends ConcreteFunctionSymbol {
    val sort = BooleanSort
    val args = List(RoundingModeSort, RoundingModeSort)
    val name = "rounding-mode-equality"
    val theory = FloatingPointTheory : Theory
  }
  // Theory constants
  //////////////////////////////////////////////////////////////////////////////
  
  // Rounding modes //
  
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

  object RoundToNegative extends RoundingMode {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToNegative"
  }
  
  object RoundToNearestTiesToAway extends RoundingMode {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToNearestTiesToAway"
  }
  
  object RoundToNearestTiesToEven extends RoundingMode {
    val sort = RoundingModeSort
    val theory = FloatingPointTheory
    val args = List()
    val name = "RoundToNearestTiesToEven"
  }
  
  // Special Values // 
  // TODO:  Keep this in mind (from the SMT-LIB standard: 
  //  "Semantically, for each eb and sb, there is exactly one +infinity value and 
  //  exactly one -infinity value in the set denoted by (_ FloatingPoint eb sb), 
  //  in agreement with the IEEE 754-2008 standard.
  //  However, +/-infinity can have two representations in this theory. 
  //  E.g., +infinity for sort (_ FloatingPoint 2 3) is represented equivalently 
  //  by (_ +oo 2 3) and (fp #b0 #b11 #b00).
  // "
  val FPPositiveZero = new FPSpecialValuesFactory("+0")
  val FPNegativeZero = new FPSpecialValuesFactory("-0")
  val FPPlusInfinity = new FPSpecialValuesFactory("+00")
  val FPMinusInfinity = new FPSpecialValuesFactory("-00")
  val FPNaN = new FPSpecialValuesFactory("NaN")
  
  
  // Operations //
  //     ; absolute value 
  //   (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPAbsFactory = new FPFunctionSymbolFactory("abs", false, 1)
  //   ; negation (no rounding needed) 
  //   (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPNegateFactory = new FPFunctionSymbolFactory("negate", false, 1)
  //   ; addition
  //   (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPAdditionFactory = new FPFunctionSymbolFactory("addition", true, 2)   
  //   ; subtraction
  //   (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPSubstractionFactory = new FPFunctionSymbolFactory("subtraction", true, 2)   
  //   ; multiplication
  //   (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPMultiplicationFactory = new FPFunctionSymbolFactory("multiplication", true, 2)     
  //   ; division
  //   (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb))
  val FPDivisionFactory = new FPFunctionSymbolFactory("division", true, 2)
  //   ; fused multiplication and addition; (x * y) + z 
  //   (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb))
  val FPFusedMultiplyAddFactory = new FPFunctionSymbolFactory("fused multiply add", true, 3)
  //   ; square root 
  //   (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPSquareRootFactory = new FPFunctionSymbolFactory("square root", true, 1)
  //   ; remainder: x - y * n, where n in Z is nearest to x/y 
  //   (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPRemainderFactory = new FPFunctionSymbolFactory("remainder", false, 2)
  //   ; rounding to integral
  //   (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPRoundToIntegralFactory = new FPFunctionSymbolFactory("round to integral", true, 1)
  //   ; minimum and maximum
  //   (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPMinimumFactory = new FPFunctionSymbolFactory("minimum", false, 2)
  //   (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPMaximumFactory = new FPFunctionSymbolFactory("maximum", false, 2)
  
  // PREDICATES //
  
  //   ; comparison operators
  //   ; Note that all comparisons evaluate to false if either argument is NaN
  //   (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val FPLessThanOrEqualFactory = new FPPredicateSymbolFactory("less-than-or-equal-to", 2)
  //   (fp.lt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val FPLessThanFactory = new FPPredicateSymbolFactory("less-than", 2)
  //   (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val FPGreaterThanOrEqualFactory = new FPPredicateSymbolFactory("greater-or-equal", 2)
  //   (fp.gt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val FPGreaterThanFactory = new FPPredicateSymbolFactory("greater-than", 2)
  //   ; IEEE 754-2008 equality (as opposed to SMT-LIB =)
  //   (fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val FPFPEqualityFactory = new FPPredicateSymbolFactory("fp-equal", 2)
  //   ; Classification of numbers

  
  val FPEqualityFactory = new FPPredicateSymbolFactory("equal", 2)
  //   ; Classification of numbers
  //   (fp.isNormal (_ FloatingPoint eb sb) Bool)
  val FPIsNormalFactory = new FPPredicateSymbolFactory("isNormal", 1)
  //   (fp.isSubnormal (_ FloatingPoint eb sb) Bool)
  val FPIsSubnormalFactory = new FPPredicateSymbolFactory("isSubnormal", 1)
  //   (fp.isZero (_ FloatingPoint eb sb) Bool)
  val FPIsZeroFactory = new FPPredicateSymbolFactory("isZero", 1)
  //   (fp.isInfinite (_ FloatingPoint eb sb) Bool)
  val FPIsInfiniteFactory = new FPPredicateSymbolFactory("isinfinite", 1)
  //   (fp.isNaN (_ FloatingPoint eb sb) Bool)
  val FPIsNaNFactory = new FPPredicateSymbolFactory("isNaN", 1)
  //   (fp.isNegative (_ FloatingPoint eb sb) Bool)
  val FPIsnegativeFactory = new FPPredicateSymbolFactory("is Negative", 1)
  //   (fp.isPositive (_ FloatingPoint eb sb) Bool)
  val FPIsPositiveFactory = new FPPredicateSymbolFactory("isPositive", 1)

  // CAST FUNCTIONS //  
  
  //   :funs_description "All function symbols with declarations of the form below
  //   where m is a numerals greater than 0 and eb, sb, mb and nb are numerals
  //   greater than 1.
  //
  //   ; from single bitstring representation in IEEE 754-2008 interchange format,
  //   ; with m = eb + sb
  //   ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))
  val IEEEInterchangeToFPFactory = new FPFunctionSymbolFactory("ieee-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  //   ; from another floating point sort
  //   ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
  val FPToFPFactory = new FPFunctionSymbolFactory("fp-to-fp", true, 1)
  //   ; from real
  //   ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
  val RealToFPFactory = new FPFunctionSymbolFactory("real-to-fp", true, 1) // TODO: This requires Reals, so it's not a pure FPOperatorSymbol
  //   ; from signed machine integer, represented as a 2's complement bit vector
  //   ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
  val SBVToFPFactory = new FPFunctionSymbolFactory("sbv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  //   ; from unsigned machine integer, represented as bit vector
  //   ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
  // "
  val UBVToFPFactory = new FPFunctionSymbolFactory("ubv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  
  //    :funs_description "All function symbols with declarations of the form below
  //   where m is a numeral greater than 0 and  eb and sb are numerals greater than 1.
  //
  //   ; to unsigned machine integer, represented as a bit vector
  //   ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
  //
  //   ; to signed machine integer, represented as a 2's complement bit vector
  //   ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m)) 
  // 
  //   ; to real
  //   (fp.to_real (_ FloatingPoint eb sb) Real)
  val FPToRealFactory = new FPToNonFPFunctionSymbolFactory("fp-to-real", false, RealTheory.RealSort) 
  // "
  // :notes
  // "All fp.to_* functions are unspecified for NaN and infinity input values.
  //  In addition, fp.to_ubv and fp.to_sbv are unspecified for finite number inputs
  //  that are out of range (which includes all negative numbers for fp.to_ubv).
  // 
  //  This means for instance that the formula
  //
  //    (= (fp.to_real (_ NaN 8 24)) (fp.to_real (fp c1 c2 c3))) 
  //
  //  is satisfiable in this theory for all binary constants c1, c2, and c3
  //  (of the proper sort). 
  // "

  
  // case class FPITE(sort : FPSort) extends PolyITE("fp-ite", sort)
  
  
  // Interface
  def fp(sign : Int, eBits : List[Int], sBits : List[Int])(implicit sort : FPSort) = {
    val factory = new FPConstantFactory(sign, eBits, sBits)
    factory(sort)
  } 
  
  def intToBits(int : Int, bitWidth : Int) = {
    (for ( i <- 0 until bitWidth) yield {
      if ((int & (1 << i )) > 0) 1 else 0
    }).reverse.toList
  }
  
  def longToBits(int : Long, bitWidth : Int) = {
    (for ( i <- 0 until bitWidth) yield {
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
  
  def doubleToBits(d : Double) = {
    val bits = java.lang.Double.doubleToLongBits(d)
    val bitList = longToBits(bits,64)
    val sign  = bitList.head
    val ebits = bitList.tail.take(11)
    val sbits = bitList.drop(12)
    (sign, ebits, sbits)
  }
  
  def bitsToDouble(fpLit : FloatingPointLiteral) : Double = {
    fpLit.getFactory match {
      case FPNaN => Double.NaN
      case FPPositiveZero => +0.0
      case FPNegativeZero => -0.0
      case FPPlusInfinity => Double.PositiveInfinity
      case FPMinusInfinity => Double.NegativeInfinity
      case FPConstantFactory(sign, eBits, sBits) => {
        fpToDouble(sign, eBits, sBits)        
      } 
    }
  }
  
  implicit def fpToAST(double : Double, sort : FPSort = FPSort(8,24)) = {
    sort match {
      case FPSort(11,53) => {
        val (sign, ebits, sbits) = doubleToBits(double)
        Leaf(fp(sign, ebits, sbits)(sort))
      }
      case FPSort(8,24) => {
        val (sign, ebits, sbits) = floatToBits(double.toFloat)
        Leaf(fp(sign, ebits, sbits)(sort))  
      }
    }
        
  }
  
  implicit def FPVarToAST(floatVar : FPVar) = Leaf(floatVar)
  implicit def RoundingModeToAST(rm : RoundingMode) = Leaf(rm)

  
  def genericOperation(left : AST, right : AST, rm : RoundingMode, factory : FPFunctionSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FPSort, r : FPSort) => {
        if (l != r)
          throw new Exception("FP-Operation of non-equal sorts!")
        val children : List[AST] = List(rm, left, right)
        AST(factory(l, l, l), children)
      }
      case _ => throw new Exception("FP-Operation of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def floatNegate(arg : AST) = 
    arg.symbol.sort match {
      case sort : FPSort => {
        val children : List[AST] = List(arg)
        AST(FPNegateFactory(sort, sort), children)
      }
      case _ => throw new Exception("FP-Operation of non-floating-point AST: " + arg)
    }
    
  def floatAddition(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPAdditionFactory)

  def floatSubtraction(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPSubstractionFactory)
    
  def floatMultiplication(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPMultiplicationFactory)
  
  def floatDivision(left: AST, right: AST)(implicit rm : RoundingMode) = 
    genericOperation(left, right, rm, FPDivisionFactory)
    
  def genericPredicate(left : AST, right : AST, factory : FPPredicateSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FPSort, r : FPSort) => {
        if (l != r)
          throw new Exception("FP-Predicate of non-equal sorts!")
        val children : List[AST] = List(left, right)
        val fpeq = factory(l)
        AST(fpeq, children)
      }
      case _ => throw new Exception("FP-Predicate of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def rmEquality(left : AST, right : AST) = 
    AST(RoundingModeEquality, List(), List(left, right))  
  
  def floatEquality(left : AST, right : AST) = 
    genericPredicate(left, right, FPEqualityFactory)

def floatFPEquality(left : AST, right : AST) = 
    genericPredicate(left, right, FPFPEqualityFactory)
    
    
  def floatLessThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, FPLessThanOrEqualFactory)
  
  def floatLessThan(left : AST, right : AST) =
    genericPredicate(left, right, FPLessThanFactory)
  
  def floatGreaterThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, FPGreaterThanOrEqualFactory)
    
  
  
 def floatGreaterThan(left : AST, right : AST) =
    genericPredicate(left, right, FPGreaterThanFactory)

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
    sum - 2.pow(bits.length - 1).toInt + 1
   }
  
  def fpToDouble(sign : Int, eBits : List[Int], sBits : List[Int]) = {   
    if( eBits.length + sBits.length + 1 > 64) 
      throw new Exception("Converting to a double fpa with more than 64 bits")
    
    val exponent = eBits.head :: List.fill(11 - eBits.length)(1 - eBits.head) ++ eBits.tail
    val significand = sBits.tail ++ List.fill(53 - sBits.length)(0)
    val bits = sign :: exponent ++ significand
    java.lang.Double.longBitsToDouble(BigInt(bits.mkString(""), 2).toLong)
//    // TODO: subnormal numbers
//    val sign = (signBit == 0)
//    val exponent = bitsToInt(eBits) - (2.pow(eBits.length - 1).toInt - 1) - sBits.length
//    val significand = bitsToInt(1 :: sBits) // Adding the implicit leading bit
//    val magnitude = if (exponent >= 0) (2.pow(exponent).toDouble) else (1.0 / (2.pow(-exponent).toDouble))
//    
//    // If denormal, etc
//    val absVal = significand * magnitude    
//    if (sign) absVal else -absVal    
  }
  
  def parseSymbol(sym : String) = {
    val bitPattern = "#b(\\d+)".r
    val hexPattern = "#x([0-9a-f]*)".r
    sym match {
      case bitPattern(b) => b.toList.map(_.toString.toInt)
      case hexPattern(h) => {
        val bits = 
          for (d <- h) yield {
            d match {
              case '0' => "0000"
              case '1' => "0001"
              case '2' => "0010"
              case '3' => "0011"
              case '4' => "0100"
              case '5' => "0101"
              case '6' => "0110"
              case '7' => "0111"
              case '8' => "1000"
              case '9' => "1001"
              case 'a' => "1010"
              case 'b' => "1011"
              case 'c' => "1100"
              case 'd' => "1101"
              case 'e' => "1110"
              case 'f' => "1111"                
            }
          }
          bits.map(_.toList).flatten.map(_.toString.toInt)
      }
      case asd => throw new Exception("parseSymbol: " + asd)
    }
  }
  
  
  def parseLiteral(lit : String) = {
    val bitPattern = """\(?fp (\S+) (\S+) ([^\s)]+)[)]*""".r
    val zeroPattern = "\\(?_ ([\\+\\-])zero (\\d+) (\\d+)\\)*".r
    val infPattern = "\\(?_ ([\\+\\-])oo (\\d+) (\\d+)\\)*".r
    val nanPattern = "\\(?_ NaN (\\d+) (\\d+)\\)*".r
    lit match {
      case "roundNearestTiesToEven" | "RNE" => RoundToNearestTiesToEven
      case "roundNearestTiesToAway" | "RNA"  => RoundToNearestTiesToAway 
      case "roundTowardPositive" | "RTP" => RoundToPositive
      case "roundTowardNegative" | "RTN"  => RoundToNegative
      case "roundTowardZero" | "RTZ" => RoundToZero      

     
      case zeroPattern(sign, eBits, sBits) => {
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        if (sign == "+") 
          Leaf(FPPositiveZero(fpsort))
        else  
          Leaf(FPNegativeZero(fpsort))
      }
      
      case infPattern(sign, eBits, sBits) => {
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        if (sign == "+")
          Leaf(FPPlusInfinity(fpsort))
        else
          Leaf(FPMinusInfinity(fpsort))
      } 
   
      case nanPattern(eBits, sBits) => {
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        Leaf(FPNaN(fpsort))        
      }
      
      case bitPattern(s1, s2, s3) => {
        val sign = 
          if (s1 == "#b0") 0
          else if (s1 == "#b1") 1
          else throw new Exception("Wrong sign bit: " + s1)
        
        val eBits = parseSymbol(s2).toList
        val sBits = parseSymbol(s3).toList
        val fpsort = FPSortFactory(List(eBits.length, sBits.length + 1))

       if (!(eBits contains 1) && !(sBits contains 1)) {
        if (sign == 0) 
          Leaf(FPPositiveZero(fpsort))
        else  
          Leaf(FPNegativeZero(fpsort))         
       } else if (!(eBits contains 0)) {
         if (!(sBits contains 1)) {
          if (sign == 0)
            Leaf(FPPlusInfinity(fpsort))
          else
            Leaf(FPMinusInfinity(fpsort))
         } else {
           Leaf(FPNaN(fpsort))        
         }
       } else {
          val constFactory = new FPConstantFactory(sign, eBits, sBits)
          Leaf(constFactory(fpsort))
       }
      }      
      
      case _ => throw new Exception("Unknown FP literal: " + lit)
    }
  }
  
//  object FPVar {
//    def apply(name : String)(implicit sort : FPSort) = {
//      new FPVar(name, sort)
//    }
    
//    def unapply(symbol : FPVar) : Option[(String, ConcreteSort)] = {
//        Some((symbol.name, symbol.sort))
//    }  
//  }
  
  // Theory shouldn't be here
  case class FPVar(val name : String, val _sort : FPSort) extends FloatingPointFunctionSymbol(_sort) {
    val args = List()
    val theory = FloatingPointTheory
    
    val getFactory = FPVarFactory(name)
  }
  
  object RMVar {
    def apply(name : String) = {
      new RMVar(name)
    }
    
    def unapply(symbol : RMVar) : Option[String] = {
        Some(symbol.name)
    }  
  }  
  
  class RMVar(val name : String) extends ConcreteFunctionSymbol {
      val args = List()
      val theory = FloatingPointTheory
      val sort = RoundingModeSort
    }  

  // TODO: What to do with this
  val sorts : List[Sort] = List()

  // TODO: How do we do this?
  val symbols = List() //: List[IndexedFunctionSymbol] = List(FPAdditionFactory.FPFunctionSymbol, FPSubtractionFactory.FPFunctionSymbol, FPEqualityFactory.FPPredicateSymbol, FPFPEqualityFactory.FPPredicateSymbol)
  
  def isLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case l : FloatingPointLiteral => true
      case rm : RoundingMode => true
      case _ => false
    }
  }
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FPVar(_, _) => false
      case RMVar(_) => false
      case _ => true
    }
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FPVar(_, _) |
           RMVar(_) => true
      case _ => false
    }
  }

  def bias(expBitWidth : Int) : Int = {
    (1 << expBitWidth - 1) - 1
  }
  
  def biasExp(exp : Int, expBitWidth : Int) : Int = {
    exp + bias(expBitWidth)
  }
  
  def biasExp(exp : List[Int], expBitWidth : Int) : Int = {
   biasExp(bitsToInt(exp), expBitWidth)
  }
  
  def unbiasExp(exp : Int, expBitWidth : Int) : Int = {
    exp - bias(expBitWidth) 
  }
  
   def unbiasExp(exp : List[Int], expBitWidth : Int) : Int = {
   unbiasExp(bitsToInt(exp), expBitWidth)
  }
  
  /** Returns a FloatingPointSymbol which corresponds to the ULP of given fpValue
   *  
   *  Given a fpValue, getULP will create a new Floating Point Symbol which 
   *  is equivalent with fpValue but will all significan bits except the last one set to 1.
   *  This corresponds to the "unit in last place" (ULP) of fpValue.
   *  
   *  If fpValue is a subnormal number the return value is undefined.
   *  
   *  @param fpValue Floating Point value of which ULP is returned.
   *  @return ULP of fpValue.
   * 
   */
  def getULP(fpValue : FloatingPointLiteral) = {
    // TODO :  Distinguish normal and subnormal numbers  
   
    val newExp = intToBits(bitsToInt(fpValue.eBits) - fpValue.sort.sBitWidth, fpValue.sort.eBitWidth)
    val newSignificand = List.fill(fpValue._sort.sBitWidth - 1)(0)
    fp(0, newExp, newSignificand) (fpValue._sort)   
  }
  
  val SMTHeader = {
    "(set-logic QF_FP)"
  }
  
  //TODO: Change to SMTLIB names
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = { 
    symbol match {      
      case FPVar(name, _) => name       
      case RoundToZero => "RTZ"
      case RoundToPositive => "RTP"
      case RoundToNegative => "RTN"
      case RoundToNearestTiesToAway => "RNA"
      case RoundToNearestTiesToEven => "RNE"
      case RoundingModeEquality => "="
      case fpFunSym : FloatingPointFunctionSymbol => {      
        fpFunSym.getFactory match {
          case FPPositiveZero => "(_ +zero " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
          case FPNegativeZero => "(_ -zero " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
          case FPPlusInfinity => "(_ +oo " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
          case FPMinusInfinity => "(_ -oo " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
          case FPNaN => "(_ NaN " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
          case FPAdditionFactory => "fp.add"
          case FPSubstractionFactory => "fp.sub"
          case FPMultiplicationFactory => "fp.mul"
          case FPDivisionFactory => "fp.div"
          case FPNegateFactory => "fp.neg"
          case FPToFPFactory => "(_ to_fp " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"         
          case FPConstantFactory(sign, eBits, sBits) => {
            val eDiff = eBits.length - fpFunSym.sort.eBitWidth
            val ebits = if (eDiff >= 0)
                          eBits.take(fpFunSym.sort.eBitWidth)
                        else
                          eBits.head :: List.fill(-eDiff)(0) ++ eBits.tail
            val sDiff = sBits.length - fpFunSym.sort.sBitWidth + 1
            val sbits = if (sDiff >= 0)
                          sBits.take(fpFunSym.sort.sBitWidth)
                        else
                          sBits ++ List.fill(-sDiff)(0) 
            
            "(fp #b" + sign + " #b" + ebits.mkString("") + " #b" + sbits.mkString("") + ")" 
          }
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
      case fpPredSym : FloatingPointPredicateSymbol => {
        fpPredSym.getFactory match {
          case FPEqualityFactory => "="
          case FPFPEqualityFactory => "fp.eq"            
          case FPLessThanOrEqualFactory => "fp.leq"
          case FPLessThanFactory => "fp.lt"
          case FPGreaterThanOrEqualFactory => "fp.geq"
          case FPGreaterThanFactory => "fp.gt"
          case FPIsZeroFactory => "fp.isZero"
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
      case uppsat.theory.FloatingPointTheory.RMVar(name) => name
     
      case other =>
        throw new FloatingPointTheoryException("Unknown symbol: " + symbol.sort)     
    }
  }
  
  
  
  def sortToSMTLib(sort : ConcreteSort)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case FPSort(e, s) => "(_ FloatingPoint " + e + " " + s + ")"
      case RoundingModeSort => "RoundingMode"
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case FPVar(name, _) => "(declare-fun " + name + " () " + sortToSMTLib(sym.sort) + ")"
      case _ => throw new Exception("Not instance of FPVar : " + sym.getClass)
    }
  }
}