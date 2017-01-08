package uppsat.theory

import uppsat.theory.BooleanTheory._
import scala.math.BigInt.int2bigInt
import uppsat.ast._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort

case class FloatingPointTheoryException(msg : String) extends Exception("Floating Point Theory Exception: " + msg)

object FloatingPointTheory extends Theory {
  val name = "FPTheory"
    
  object FPSortFactory extends IndexedSortFactory { 
    case class FPSort(eBits : Int, sBits : Int) extends IndexedSort {
      val name = "Floating Point (" + eBits + ", " + sBits + ")"
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
  
  abstract class FloatingPointFunctionSymbol(val sort : FPSort) extends IndexedFunctionSymbol
  abstract class FloatingPointConstantSymbol(override val sort : FPSort) extends FloatingPointFunctionSymbol(sort)
  abstract class FloatingPointLiteral(override val sort : FPSort, val sign : Int, val eBits : List[Int], val sBits : List[Int]) extends FloatingPointFunctionSymbol(sort)
  abstract class FloatingPointPredicateSymbol extends IndexedFunctionSymbol
  
  
  case class FPOperatorSymbolFactory(symbolName : String, isRounding : Boolean, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
    case class FPFunctionSymbol(val args : Seq[ConcreteSort], override val sort : FPSort) extends FloatingPointFunctionSymbol(sort) {   
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val name = symbolName
    }
    
    val arity = 1 // Refers to the sorts
    def apply(sorts : Seq[ConcreteSort]) = {
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

    val arity = 1 // Refers to the sorts
    override def apply(sort : Seq[ConcreteSort]) = {      
      FPPredicateSymbol(sort.head)  
    }
  }

  // TODO: Bitset instead of List[Int]
  case class FPConstantFactory(sign : Int, eBits: List[Int], sBits : List[Int]) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPConstantSymbol(override val sort : FPSort) extends FloatingPointLiteral(sort, sign, eBits.take(sort.eBits), sBits.take(sort.sBits - 1)) {
      // TODO: Does name have to be SMT-appliant, not nice!
      val name = fpToFloat(sign, eBits, sBits).toString() 
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val args = List()
    }

    val arity = 1 // Refers to the sorts
    // TODO:  Change to repeated arguments
    override def apply(sort : Seq[ConcreteSort]) = {
      sort.head match {
        case fpsort : FPSort => {          
          FPConstantSymbol(fpsort)
        }
        case _ =>  throw new Exception("Non-FP sort : " + sort.head)
      }  
    }    
  }

case class FPSpecialValuesFactory(symbolName : String) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    case class FPConstantSymbol(override val sort : FPSort) extends FloatingPointConstantSymbol(sort) {
      val theory = FloatingPointTheory
      val getFactory = thisFactory
      val name = symbolName
      val args = List()
    }
    
    val arity = 1 // Refers to the sorts
    override def apply(sort : Seq[ConcreteSort]) = {
      sort match {
        case List(fpsort : FPSort) => {      
          FPConstantSymbol(fpsort)
        }
        case _ =>  throw new Exception("Non-FP singleton sort in special values  : " + sort.head)
      }  
    }
  }

  
  // TODO: Change to BigInt
  def FPLiteral(sign : Int, eBits : List[Int], sBits : List[Int], sort : FPSort) = {
    val newFactory = new FPConstantFactory(sign, eBits, sBits)
    if (sort.eBits != eBits.length || sort.sBits != sBits.length + 1) {
      throw new Exception("Creating literal with wrong sort? " + sort + ", " + eBits + ", " + sBits)
    }
    newFactory(List(sort))
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
  
  object RoundingModeEquality extends ConcreteFunctionSymbol {
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
  val FPAbsFactory = new FPOperatorSymbolFactory("abs", false, 1)
  //   ; negation (no rounding needed) 
  //   (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPNegateFactory = new FPOperatorSymbolFactory("negate", false, 1)
  //   ; addition
  //   (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPAdditionFactory = new FPOperatorSymbolFactory("addition", true, 2)   
  //   ; subtraction
  //   (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPSubstractionFactory = new FPOperatorSymbolFactory("subtraction", true, 2)   
  //   ; multiplication
  //   (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb)) 
  val FPMultiplicationFactory = new FPOperatorSymbolFactory("multiplication", true, 2)     
  //   ; division
  //   (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb))
  val FPDivisionFactory = new FPOperatorSymbolFactory("division", true, 2)
  //   ; fused multiplication and addition; (x * y) + z 
  //   (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
  //     (_ FloatingPoint eb sb))
  val FPFusedMultiplyAddFactory = new FPOperatorSymbolFactory("fused multiply add", true, 3)
  //   ; square root 
  //   (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPSquareRootFactory = new FPOperatorSymbolFactory("square root", true, 1)
  //   ; remainder: x - y * n, where n in Z is nearest to x/y 
  //   (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPRemainderFactory = new FPOperatorSymbolFactory("remainder", false, 2)
  //   ; rounding to integral
  //   (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPRoundToIntegralFactory = new FPOperatorSymbolFactory("round to integral", true, 1)
  //   ; minimum and maximum
  //   (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPMinimumFactory = new FPOperatorSymbolFactory("minimum", false, 2)
  //   (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val FPMaximumFactory = new FPOperatorSymbolFactory("maximum", false, 2)
  
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
  val IEEEInterchangeToFPFactory = new FPOperatorSymbolFactory("ieee-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  //   ; from another floating point sort
  //   ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
  val FPToFPFactory = new FPOperatorSymbolFactory("fp-to-fp", true, 1)
  //   ; from real
  //   ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
  val RealToFPFactory = new FPOperatorSymbolFactory("real-to-fp", true, 1) // TODO: This requires Reals, so it's not a pure FPOperatorSymbol
  //   ; from signed machine integer, represented as a 2's complement bit vector
  //   ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
  val SBVToFPFactory = new FPOperatorSymbolFactory("sbv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  //   ; from unsigned machine integer, represented as bit vector
  //   ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
  // "
  val UBVToFPFactory = new FPOperatorSymbolFactory("ubv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
  
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
      case _ => throw new Exception("FP-Operation of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def floatNegate(arg : AST) = 
    arg.symbol.sort match {
      case sort : FPSort => {
        val children : List[AST] = List(arg)
        AST(FPNegateFactory(List(sort, sort)), children)
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
        val fpeq = factory(List(l))
        AST(fpeq, children)
      }
      case _ => throw new Exception("FP-Predicate of non-floating-point AST: " + left + " and " + right)
    }  
  }
  
  def rmEquality(left : AST, right : AST) = 
    AST(RoundingModeEquality, List(), List(left, right))  
  
  def floatEquality(left : AST, right : AST) = 
    genericPredicate(left, right, FPEqualityFactory)

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
    if (bits.head == 0) {
      sum - 2.pow(bits.length - 1).toInt
    } else {
      sum
    }        
   }
  
  def fpToFloat(signBit : Int, eBits : List[Int], sBits : List[Int]) = {
    val sign = (signBit == 0)
    val exponent = bitsToInt(eBits) - (2.pow(eBits.length - 1).toInt - 1)
    val significand = sbitsToFloat(sBits)
    val magnitude = if (exponent >= 0) (2.pow(exponent).toInt) else (1.0 / (2.pow(-exponent).toInt))
    // If denormal, etc
    val absVal = (1 + significand) * magnitude
    if (sign) absVal else -absVal    
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
    val bitPattern = "\\(fp (\\S*) (\\S*) (\\S*)\\)".r
    val zeroPattern = "\\(_ ([\\+\\-])zero (\\d+) (\\d+)\\)".r
    val infPattern = "\\(_ ([\\+\\-])oo (\\d+) (\\d+)\\)".r
    val nanPattern = "\\(_ NaN (\\d+) (\\d+)\\)".r
    lit match {
      case "roundNearestTiesToEven" => RoundToNearestTiesToEven
      case "roundNearestTiesToAway" => RoundToNearestTiesToAway 
      case "roundTowardPositive" => RoundToPositive
      case "roundTowardNegative" => RoundToNegative
      case "roundTowardZero" => RoundToZero      

      case bitPattern(s1, s2, s3) => {
        val sign = 
          if (s1 == "#b0") 0
          else if (s1 == "#b1") 1
          else throw new Exception("Wrong sign bit: " + s1)
        
        val eBits = parseSymbol(s2).toList
        val sBits = parseSymbol(s3).toList
        val constFactory = new FPConstantFactory(sign, eBits, sBits)
        val fpsort = FPSortFactory(List(eBits.length, sBits.length + 1))
        Leaf(constFactory(List(fpsort)))
      }
      case zeroPattern(sign, eBits, sBits) => {
        val signBit = if (sign == "+") 0 else 1
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        // TODO: Aleks, is the number of zeroes correct?
        val factory = new FPConstantFactory(signBit, List.fill(eBits.toInt)(0), List.fill(sBits.toInt - 1)(0))
        Leaf(factory(List(fpsort)))
      }
      case infPattern(sign, eBits, sBits) => {
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        if (sign == "+")
          Leaf(FPPlusInfinity(List(fpsort)))
        else
          Leaf(FPMinusInfinity(List(fpsort)))
      } 
      case nanPattern(eBits, sBits) => {
        // TODO: Have special representation for NaN
        val signBit = 0
        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
        // TODO: Aleks, is the number of zeroes correct?
        val factory = new FPConstantFactory(signBit, List.fill(eBits.toInt)(0), List.fill(sBits.toInt - 1)(0))
        Leaf(factory(List(fpsort)))        
      }
      case _ => throw new Exception("Unknown FP literal: " + lit)
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
  
  // Theory shouldn't be here
  class FPVar(val name : String, val sort : FPSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = FloatingPointTheory
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
  val symbols = List() //: List[IndexedFunctionSymbol] = List(FPAdditionFactory.FPFunctionSymbol, FPSubtractionFactory.FPFunctionSymbol, FPEqualityFactory.FPPredicateSymbol)
  
  def isLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case l : FloatingPointLiteral => true
      case rm : RoundingMode => true
      case _ => false
    }
  }
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FPVar(_) => false
      case RMVar(_) => false
      case _ => true
    }
  }
  
  val SMTHeader = {
    "(set-logic QF_FP)" //TODO: Check the actual logic
  }
  
  //TODO: Change to SMTLIB names
  def toSMTLib(symbol : ConcreteFunctionSymbol) = { 
    symbol match {
      case RoundToZero => "RTZ"
      case RoundToPositive => "RTP"
      case RoundToNegative => "RTN"
      case RoundToNearestTiesToAway => "RNA"
      case RoundToNearestTiesToEven => "RNE"
      case RoundingModeEquality => "="
      case fpFunSym : FloatingPointFunctionSymbol => {      
        fpFunSym.getFactory match {
          case FPPositiveZero => "+0"
          case FPPlusInfinity => "(_ +oo " + fpFunSym.sort.eBits + " " + fpFunSym.sort.sBits + ")"
          case FPMinusInfinity => "(_ -oo " + fpFunSym.sort.eBits + " " + fpFunSym.sort.sBits + ")"
          case FPAdditionFactory => "fp.add"
          case FPSubstractionFactory => "fp.sub"
          case FPMultiplicationFactory => "fp.mul"
          case FPDivisionFactory => "fp.div"
          case FPNegateFactory => "fp.neg"
          case FPToFPFactory => "(_ to_fp " + fpFunSym.sort.eBits + " " + fpFunSym.sort.sBits + ")"          
          case FPConstantFactory(sign, eBits, sBits) => {
            "(fp #b" + sign + " #b" + eBits.take(fpFunSym.sort.eBits).mkString("") + " #b" + sBits.take(fpFunSym.sort.sBits - 1).mkString("") + ")" 
          }
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
      case fpPredSym : FloatingPointPredicateSymbol => {
        fpPredSym.getFactory match {
          case FPEqualityFactory => "="
          case FPLessThanOrEqualFactory => "fp.leq"
          case FPLessThanFactory => "fp.lt"
          case FPGreaterThanOrEqualFactory => "fp.geq"
          case FPGreaterThanFactory => "fp.gt"
          case str => throw new Exception("Unsupported FP symbol: " + str)
        }
      }
      case uppsat.theory.FloatingPointTheory.RMVar(name) => name
      case FPVar(name, _) => name
      case other => throw new FloatingPointTheoryException("Unknown symbol: " + symbol)      
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