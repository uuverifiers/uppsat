package uppsat.theory

import uppsat.theory.BooleanTheory._
import uppsat.ast._
import uppsat.theory.BitVectorTheory.BVSortFactory.BVSort
case class BitVectorTheoryException(msg : String) extends Exception("BitVector Theory Exception: " + msg)

object BitVectorTheory extends Theory {
  val name = "BVTheory"
  
  
  object BVSortFactory extends IndexedSortFactory { 
    case class BVSort(bitWidth : Int) extends IndexedSort {
      val name = "BitVector (" + bitWidth + ")"
      val theory = BitVectorTheory
      val getFactory = BVSortFactory
      
      if (bitWidth < 1)
        throw new BitVectorTheoryException("Negative bit-count: " + bitWidth)        
    }
  
    val arity = 1 
    def apply(idx : Seq[BigInt]) = {
      val bits = idx(0).toInt
      if (bits < 1)
        throw new BitVectorTheoryException("Negative bit-count: " + bits)
      // TODO: Use HashTable to store and re-use
      BVSort(bits)
    }
  }
//  
  abstract class BitVectorSymbol extends IndexedFunctionSymbol
  abstract class BitVectorFunctionSymbol(val sort : BVSort) extends BitVectorSymbol
  abstract class BitVectorPredicateSymbol extends BitVectorSymbol
  abstract class FloatingPointConstantSymbol(override val sort : BVSort) extends BitVectorFunctionSymbol(sort)
  

  abstract class BVGenConstantFactory extends IndexedFunctionSymbolFactory {
    def getName(sort : BVSort) : String
  }

object BitVectorLiteral {
    def apply(bits : List[Int], sort : BVSort) : BitVectorLiteral = {
      val newFactory = new BVConstantFactory(bits)
      if (sort.bitWidth != bits.length)
        throw new BitVectorTheoryException("Creating literal with wrong sort? " + sort + ", " + bits)

      newFactory(sort).asInstanceOf[BitVectorLiteral]
    }
  }
//
  case class BitVectorLiteral(_sort : BVSort, getFactory : BVGenConstantFactory)
             extends FloatingPointConstantSymbol(_sort) {
    val name = getFactory getName sort
    val theory = BitVectorTheory
    val args = List()
    lazy val bits = getFactory.asInstanceOf[BVConstantFactory].bits
  }
  
  case class BVFunctionSymbol(val args : Seq[ConcreteSort], _sort : BVSort, val getFactory : BVFunctionSymbolFactory) 
             extends BitVectorFunctionSymbol(_sort) {   
    val theory = BitVectorTheory
    val name = getFactory symbolName
  }
  
  case class BVPredicateSymbol( val argSort : ConcreteSort, val getFactory : BVPredicateSymbolFactory) extends BitVectorPredicateSymbol {   
    val theory = BitVectorTheory    
    val name = getFactory.symbolName
    val sort = BooleanSort
    val args = List.fill(getFactory.bvArity)(argSort)
  }
  
  case class BVFunctionSymbolFactory(symbolName : String, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    val arity = 1 // Refers to the sorts
    def apply(sorts : ConcreteSort*) = {
      sorts.reverse.head match {
        case bvsort : BVSort => {      
          val argSorts = sorts.take(sorts.length - 1).toList
          val args = argSorts
          BVFunctionSymbol(args, bvsort, this)
        }
        case _ =>  throw new Exception("Non-BV sort : " + sorts.head)
      }  
    }
  }

  case class BVPredicateSymbolFactory(symbolName : String, bvArity : Int) extends IndexedFunctionSymbolFactory {
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {      
      BVPredicateSymbol(sort.head, this)  
    }
  }
//
//  // TODO: Bitset instead of List[Int]
  case class BVConstantFactory(bits : List[Int]) extends BVGenConstantFactory {
    val thisFactory = this

    def getName(sort : BVSort) = {
      bits.mkString("")
    }
    
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {
      sort.head match {
        case bvsort : BVSort =>
          BitVectorLiteral(bvsort, this)
        case _ =>  throw new BitVectorTheoryException("Non-BV sort : " + sort.head)
      }  
    }    
  }
//
//case class FPSpecialValuesFactory(symbolName : String) extends FPGenConstantFactory {
//    val thisFactory = this
//
//    def getName(sort : FPSort) = symbolName
//    
//    val arity = 1 // Refers to the sorts
//    override def apply(sort : Seq[ConcreteSort]) = {
//      sort match {
//        case List(fpsort : FPSort) => {      
//          FloatingPointLiteral(fpsort, this)
//        }
//        case _ =>  throw new Exception("Non-FP singleton sort in special values  : " + sort.head)
//      }  
//    }
//  }
//
//  
//  /////////////////////////////////////////////  
//  // SMT-LIB SUPPORTED SYMBOLS
//  /////////////////////////////////////////////
//  
//  
//  // SORTS 
//  object RoundingModeSort extends ConcreteSort {
//    val name = "RoundingMode"
//    val theory = FloatingPointTheory : Theory
//  } 
//  
//  abstract class RoundingMode extends ConcreteFunctionSymbol
//  
//  case object RoundingModeEquality extends ConcreteFunctionSymbol {
//    val sort = BooleanSort
//    val args = List(RoundingModeSort, RoundingModeSort)
//    val name = "rounding-mode-equality"
//    val theory = FloatingPointTheory : Theory
//  }
//  // Theory constants
//  //////////////////////////////////////////////////////////////////////////////
//  
//  // Rounding modes //
//  
//  object RoundToZero extends RoundingMode {
//    val sort = RoundingModeSort
//    val theory = FloatingPointTheory
//    val args = List()
//    val name = "RoundToZero"
//  }
//
//  object RoundToPositive extends RoundingMode {
//    val sort = RoundingModeSort
//    val theory = FloatingPointTheory
//    val args = List()
//    val name = "RoundToPositive"
//  }
//
//  object RoundToNegative extends RoundingMode {
//    val sort = RoundingModeSort
//    val theory = FloatingPointTheory
//    val args = List()
//    val name = "RoundToNegative"
//  }
//  
//  object RoundToNearestTiesToAway extends RoundingMode {
//    val sort = RoundingModeSort
//    val theory = FloatingPointTheory
//    val args = List()
//    val name = "RoundToNearestTiesToAway"
//  }
//  
//  object RoundToNearestTiesToEven extends RoundingMode {
//    val sort = RoundingModeSort
//    val theory = FloatingPointTheory
//    val args = List()
//    val name = "RoundToNearestTiesToEven"
//  }
//  
//  // Special Values // 
//  // TODO:  Keep this in mind (from the SMT-LIB standard: 
//  //  "Semantically, for each eb and sb, there is exactly one +infinity value and 
//  //  exactly one -infinity value in the set denoted by (_ FloatingPoint eb sb), 
//  //  in agreement with the IEEE 754-2008 standard.
//  //  However, +/-infinity can have two representations in this theory. 
//  //  E.g., +infinity for sort (_ FloatingPoint 2 3) is represented equivalently 
//  //  by (_ +oo 2 3) and (fp #b0 #b11 #b00).
//  // "
//  val FPPositiveZero = new FPSpecialValuesFactory("+0")
//  val FPNegativeZero = new FPSpecialValuesFactory("-0")
//  val FPPlusInfinity = new FPSpecialValuesFactory("+00")
//  val FPMinusInfinity = new FPSpecialValuesFactory("-00")
//  val FPNaN = new FPSpecialValuesFactory("NaN")
//  
//  
//  // Operations //
//  //     ; absolute value 
//  //   (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPAbsFactory = new FPFunctionSymbolFactory("abs", false, 1)
//  //   ; negation (no rounding needed) 
//  //   (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
  val BVNotFactory = new BVFunctionSymbolFactory("not", 1)
//  //   ; addition
//  //   (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
//  //     (_ FloatingPoint eb sb)) 
//  val FPAdditionFactory = new FPFunctionSymbolFactory("addition", true, 2)   
//  //   ; subtraction
//  //   (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
//  //     (_ FloatingPoint eb sb)) 
//  val FPSubstractionFactory = new FPFunctionSymbolFactory("subtraction", true, 2)   
//  //   ; multiplication
//  //   (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
//  //     (_ FloatingPoint eb sb)) 
//  val FPMultiplicationFactory = new FPFunctionSymbolFactory("multiplication", true, 2)     
//  //   ; division
//  //   (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
//  //     (_ FloatingPoint eb sb))
//  val FPDivisionFactory = new FPFunctionSymbolFactory("division", true, 2)
//  //   ; fused multiplication and addition; (x * y) + z 
//  //   (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
//  //     (_ FloatingPoint eb sb))
//  val FPFusedMultiplyAddFactory = new FPFunctionSymbolFactory("fused multiply add", true, 3)
//  //   ; square root 
//  //   (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPSquareRootFactory = new FPFunctionSymbolFactory("square root", true, 1)
//  //   ; remainder: x - y * n, where n in Z is nearest to x/y 
//  //   (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPRemainderFactory = new FPFunctionSymbolFactory("remainder", false, 2)
//  //   ; rounding to integral
//  //   (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPRoundToIntegralFactory = new FPFunctionSymbolFactory("round to integral", true, 1)
//  //   ; minimum and maximum
//  //   (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPMinimumFactory = new FPFunctionSymbolFactory("minimum", false, 2)
//  //   (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
//  val FPMaximumFactory = new FPFunctionSymbolFactory("maximum", false, 2)
//  
//  // PREDICATES //
//  
//  //   ; comparison operators
//  //   ; Note that all comparisons evaluate to false if either argument is NaN
//  //   (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
//  val FPLessThanOrEqualFactory = new FPPredicateSymbolFactory("less-than-or-equal-to", 2)
  val BVLessThanOrEqualFactory = new BVPredicateSymbolFactory("less-than-or-equal", 2)
//  //   (fp.lt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
  val BVLessThanFactory = new BVPredicateSymbolFactory("less-than", 2)
  //   (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
//  val FPGreaterThanOrEqualFactory = new FPPredicateSymbolFactory("greater-or-equal", 2)
//  //   (fp.gt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
//  val FPGreaterThanFactory = new FPPredicateSymbolFactory("greater-than", 2)
//  //   ; IEEE 754-2008 equality (as opposed to SMT-LIB =)
//  //   (fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable) 
  val BVEqualityFactory = new BVPredicateSymbolFactory("equal", 2)
//  //   ; Classification of numbers
//  //   (fp.isNormal (_ FloatingPoint eb sb) Bool)
//  val FPIsNormalFactory = new FPPredicateSymbolFactory("isNormal", 1)
//  //   (fp.isSubnormal (_ FloatingPoint eb sb) Bool)
//  val FPIsSubnormalFactory = new FPPredicateSymbolFactory("isSubnormal", 1)
//  //   (fp.isZero (_ FloatingPoint eb sb) Bool)
//  val FPIsZeroFactory = new FPPredicateSymbolFactory("isZero", 1)
//  //   (fp.isInfinite (_ FloatingPoint eb sb) Bool)
//  val FPIsInfiniteFactory = new FPPredicateSymbolFactory("isinfinite", 1)
//  //   (fp.isNaN (_ FloatingPoint eb sb) Bool)
//  val FPIsNaNFactory = new FPPredicateSymbolFactory("isNaN", 1)
//  //   (fp.isNegative (_ FloatingPoint eb sb) Bool)
//  val FPIsnegativeFactory = new FPPredicateSymbolFactory("is Negative", 1)
//  //   (fp.isPositive (_ FloatingPoint eb sb) Bool)
//  val FPIsPositiveFactory = new FPPredicateSymbolFactory("isPositive", 1)
//
//  // CAST FUNCTIONS //  
//  
//  //   :funs_description "All function symbols with declarations of the form below
//  //   where m is a numerals greater than 0 and eb, sb, mb and nb are numerals
//  //   greater than 1.
//  //
//  //   ; from single bitstring representation in IEEE 754-2008 interchange format,
//  //   ; with m = eb + sb
//  //   ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))
//  val IEEEInterchangeToFPFactory = new FPFunctionSymbolFactory("ieee-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
//  //   ; from another floating point sort
//  //   ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
  object BVZeroExtendFactory {
    def apply(count : Int) = {
      new BVZeroExtendFactory(count)
    }
  }
  
  class BVZeroExtendFactory(val count : Int) extends BVFunctionSymbolFactory("zero_extend", 1)
  
  object BVSignExtendFactory {
    def apply(count : Int) = {
      new BVSignExtendFactory(count)
    }
  }
  
  class BVSignExtendFactory(val count : Int) extends BVFunctionSymbolFactory("sign_extend", 1) {

  }
  
  object BVExtractFactory {
    def apply(startBit : Int, endBit : Int) = {
      new BVExtractFactory(startBit, endBit)
    }
  }
  class BVExtractFactory(val startBit : Int, val endBit : Int) extends BVFunctionSymbolFactory("extract", 1) {
    
  }
  val BVAndFactory = new BVFunctionSymbolFactory("bvAnd", 2)
  
  val BVAddFactory = new BVFunctionSymbolFactory("bvAdd", 2)
  val BVMulFactory = new BVFunctionSymbolFactory("bvMul", 2)
  val BVDivFactory = new BVFunctionSymbolFactory("bvDiv", 2)
  val BVAshrFactory = new BVFunctionSymbolFactory("bvAshr", 2)
  
  
  val BVOrFactory = new BVFunctionSymbolFactory("bvOr", 2)
  val BVXorFactory = new BVFunctionSymbolFactory("bvXor", 2)  
  val BVConcatFactory = new BVFunctionSymbolFactory("concat", 2)  
//  //   ; from real
//  //   ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
//  val RealToFPFactory = new FPFunctionSymbolFactory("real-to-fp", true, 1) // TODO: This requires Reals, so it's not a pure FPOperatorSymbol
//  //   ; from signed machine integer, represented as a 2's complement bit vector
//  //   ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
//  val SBVToFPFactory = new FPFunctionSymbolFactory("sbv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
//  //   ; from unsigned machine integer, represented as bit vector
//  //   ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
//  // "
//  val UBVToFPFactory = new FPFunctionSymbolFactory("ubv-to-fp", true, 1) // TODO: This requires Bit-Vectors, so it's not a pure FPOperatorSymbol
//  
//  //    :funs_description "All function symbols with declarations of the form below
//  //   where m is a numeral greater than 0 and  eb and sb are numerals greater than 1.
//  //
//  //   ; to unsigned machine integer, represented as a bit vector
//  //   ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
//  //
//  //   ; to signed machine integer, represented as a 2's complement bit vector
//  //   ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m)) 
//  //
//  //   ; to real
//  //   (fp.to_real (_ FloatingPoint eb sb) Real)
//  // "
//  // :notes
//  // "All fp.to_* functions are unspecified for NaN and infinity input values.
//  //  In addition, fp.to_ubv and fp.to_sbv are unspecified for finite number inputs
//  //  that are out of range (which includes all negative numbers for fp.to_ubv).
//  // 
//  //  This means for instance that the formula
//  //
//  //    (= (fp.to_real (_ NaN 8 24)) (fp.to_real (fp c1 c2 c3))) 
//  //
//  //  is satisfiable in this theory for all binary constants c1, c2, and c3
//  //  (of the proper sort). 
//  // "
//
//  
//  // case class FPITE(sort : FPSort) extends PolyITE("fp-ite", sort)
//  
//  
  // Interface
  def bv(bitlist : List[Int])(implicit sort : BVSort) = {
    val factory = new BVConstantFactory(bitlist)
    factory(sort)
  } 
//  
//  def intToBits(int : Int, bitWidth : Int) = {
//    (for ( i <- 0 until bitWidth) yield {
//      if ((int & (1 << i )) > 0) 1 else 0
//    }).reverse.toList
//  }
//  
//  def floatToBits(f : Float) = {
//    val bits = java.lang.Float.floatToIntBits(f)
//    val bitList = intToBits(bits,32)
//    val sign  = bitList.head //intToBits(bits & 0x80000000, 1)
//    val ebits = bitList.tail.take(8)//intToBits(bits & 0x7f800000, 8)
//    val sbits = bitList.drop(9)//intToBits(bits & 0x007fffff, 23)
//    (sign, ebits, sbits)
//  }
//  
//  def bitsToDouble(fpLit : FloatingPointLiteral) : Double = {
//    fpLit.getFactory match {
//      case FPNaN => Double.NaN
//      case FPPositiveZero => +0.0
//      case FPNegativeZero => -0.0
//      case FPPlusInfinity => Double.PositiveInfinity
//      case FPMinusInfinity => Double.NegativeInfinity
//      case FPConstantFactory(sign, eBits, sBits) => {
//        //padding to a double
//        if( eBits.length + sBits.length + 1 > 64) 
//          throw new Exception("Converting to a double fpa with more than 64 bits")
//        
//        val exponent = eBits.head :: List.fill(11 - eBits.length)(0) ++ eBits.tail
//        val significand = List.fill(53 - sBits.length)(0) ++ sBits
//        val bits = sign :: exponent ++ significand
//        java.lang.Double.longBitsToDouble(BigInt(bits.mkString(""), 2).toLong)        
//      } 
//    }
//  }
//  
//  implicit def floatToAST(float : Float) = {
//    val sort = FPSortFactory(List(8,24))
//    val (sign, ebits, sbits) = floatToBits(float)
//    Leaf(fp(sign, ebits, sbits)(sort))    
//  }
//  
//  def floatToAST(float : Float, sort : FPSort) = {
//    val (sign, ebits, sbits) = floatToBits(float)
//    Leaf(fp(sign, ebits, sbits)(sort))    
//  }
//  
//  implicit def FPVarToAST(floatVar : FPVar) = Leaf(floatVar)
//  implicit def RoundingModeToAST(rm : RoundingMode) = Leaf(rm)
//
//  
  def genericOperation(left : AST, right : AST, factory : BVFunctionSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : BVSort, r : BVSort) => {
        if (l != r)
          throw new Exception("BV-Operation of non-equal sorts: " + l + " & " + r)
        val children : List[AST] = List(left, right)
        AST(factory(l, l, l), children)
      }
      case _ => throw new Exception("BV-Operation of non-BitVector-point AST: " + left + " and " + right)
    }  
  }

  def bvExtract(startBit : Int, endBit : Int, arg : AST) = {
    arg.symbol.sort match {
      case sort : BVSort => {
        val children : List[AST] = List(arg)
        val newSort = BVSort(endBit - startBit + 1)
        val newSymbol = BVExtractFactory(startBit, endBit)(newSort)
        AST(newSymbol, children)
      }
      case _ => throw new Exception("BV-Operation of non-BitVector-point AST: " + arg)
    }
  }  
  
  def bvConcat(left : AST, right : AST) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (BVSort(bits), BVSort(bits2)) => {
        val newSort = BVSort(bits + bits2)
        val newSymbol = BVConcatFactory(newSort)
        AST(newSymbol, List(left, right))
      }
      case _ => throw new Exception("Concat of non-Bitvector children: " + left.symbol.sort + ", " + right.symbol.sort)
    }
  }
  
  def bvNot(arg : AST) = {
    arg.symbol.sort match {
      case sort : BVSort => {
        val children : List[AST] = List(arg)
        AST(BVNotFactory(sort), children)
      }
      case _ => throw new Exception("BV-Operation of non-BitVector-point AST: " + arg)
    }
  }

  def bvOr(left : AST, right : AST) = 
    genericOperation(left, right, BVOrFactory)  

  def bvXor(left : AST, right : AST) = 
  genericOperation(left, right, BVXorFactory)  
  
  def bvAnd(left : AST, right : AST) = 
    genericOperation(left, right, BVAndFactory)  


  def bvAdd(left : AST, right : AST) = 
    genericOperation(left, right, BVAddFactory)  
    
    
  def bvMul(left : AST, right : AST) = 
    genericOperation(left, right, BVMulFactory)  

  def bvDiv(left : AST, right : AST) = 
    genericOperation(left, right, BVDivFactory)  
    
    
  def bvAshr(left : AST, right : AST) = 
    genericOperation(left, right, BVAshrFactory)  
    
    
//  
//  def floatNegate(arg : AST) = 
//    arg.symbol.sort match {
//      case sort : FPSort => {
//        val children : List[AST] = List(arg)
//        AST(FPNegateFactory(List(sort, sort)), children)
//      }
//      case _ => throw new Exception("FP-Operation of non-floating-point AST: " + arg)
//    }
//    
//  def floatAddition(left: AST, right: AST)(implicit rm : RoundingMode) = 
//    genericOperation(left, right, rm, FPAdditionFactory)
//
//  def floatSubtraction(left: AST, right: AST)(implicit rm : RoundingMode) = 
//    genericOperation(left, right, rm, FPSubstractionFactory)
//    
//  def floatMultiplication(left: AST, right: AST)(implicit rm : RoundingMode) = 
//    genericOperation(left, right, rm, FPMultiplicationFactory)
//  
//  def floatDivision(left: AST, right: AST)(implicit rm : RoundingMode) = 
//    genericOperation(left, right, rm, FPDivisionFactory)
//    
  
  // TODO: Maybe this can be placed somewhere more generic?
  def genericPredicate(left : AST, right : AST, factory : BVPredicateSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : BVSort, r : BVSort) => {
        if (l != r)
          throw new Exception("BV-Predicate of non-equal sorts: " + l + " & " + r)
        val children : List[AST] = List(left, right)
        val fpeq = factory(l)
        AST(fpeq, children)
      }
      case _ => throw new Exception("BV-Predicate of non-floating-point AST: " + left + " and " + right)
    }  
  }
//  
//  def rmEquality(left : AST, right : AST) = 
//    AST(RoundingModeEquality, List(), List(left, right))  
//  
  def bvEquality(left : AST, right : AST) = 
    genericPredicate(left, right, BVEqualityFactory)
//
//  def floatLessThanOrEqual(left : AST, right : AST) =
//    genericPredicate(left, right, FPLessThanOrEqualFactory)
//  

  def bvLessThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, BVLessThanOrEqualFactory)
    
  def bvLessThan(left : AST, right : AST) =
    genericPredicate(left, right, BVLessThanFactory)
//  
//  def floatGreaterThanOrEqual(left : AST, right : AST) =
//    genericPredicate(left, right, FPGreaterThanOrEqualFactory)
//    
//  
//  
// def floatGreaterThan(left : AST, right : AST) =
//    genericPredicate(left, right, FPGreaterThanFactory)
//
//  def bitsToInt(bits : List[Int]) : Int = {
//    def bti(bs : List[Int], exp : Int, ack : Int) : Int = {
//      bs match {
//        case Nil => ack
//        case 0 :: tail => bti(tail, exp*2, ack)
//        case 1 :: tail => bti(tail, exp*2, ack+exp)
//        case _ => throw new Exception("List contains non-binary digit: " + bs)
//      }
//    }
//    bti(bits.reverse, 1, 0)
//  }
//  
//  def sbitsToFloat(bits : List[Int]) : Float = {
//    def bti(bs : List[Int], exp : Float, ack : Float) : Float = {
//      bs match {
//        case Nil => ack
//        case 0 :: tail => bti(tail, exp/2, ack)
//        case 1 :: tail => bti(tail, exp/2, ack+exp)
//        case _ => throw new Exception("List contains non-binary digit: " + bs)
//      }
//    }
//    bti(bits, 0.5f, 0)
//  }
//  
//  def ebitsToInt(bits : List[Int]) : Int = {
//    val sum = bitsToInt(bits.tail.reverse)
//    if (bits.head == 0) {
//      sum - 2.pow(bits.length - 1).toInt
//    } else {
//      sum
//    }        
//   }
//  
//  def fpToDouble(signBit : Int, eBits : List[Int], sBits : List[Int]) = {
//    // TODO: subnormal numbers
//    val sign = (signBit == 0)
//    val exponent = bitsToInt(eBits) - (2.pow(eBits.length - 1).toInt - 1) - sBits.length
//    val significand = bitsToInt(1 :: sBits) // Adding the implicit leading bit
//    val magnitude = if (exponent >= 0) (2.pow(exponent).toDouble) else (1.0 / (2.pow(-exponent).toDouble))
//    
//    // If denormal, etc
//    val absVal = significand * magnitude    
//    if (sign) absVal else -absVal    
//  }
//  
//  def parseSymbol(sym : String) = {
//    val bitPattern = "#b(\\d+)".r
//    val hexPattern = "#x([0-9a-f]*)".r
//    sym match {
//      case bitPattern(b) => b.toList.map(_.toString.toInt)
//      case hexPattern(h) => {
//        val bits = 
//          for (d <- h) yield {
//            d match {
//              case '0' => "0000"
//              case '1' => "0001"
//              case '2' => "0010"
//              case '3' => "0011"
//              case '4' => "0100"
//              case '5' => "0101"
//              case '6' => "0110"
//              case '7' => "0111"
//              case '8' => "1000"
//              case '9' => "1001"
//              case 'a' => "1010"
//              case 'b' => "1011"
//              case 'c' => "1100"
//              case 'd' => "1101"
//              case 'e' => "1110"
//              case 'f' => "1111"                
//            }
//          }
//          bits.map(_.toList).flatten.map(_.toString.toInt)
//      }
//      case asd => throw new Exception("parseSymbol: " + asd)
//    }
//  }
//  
//  
    
  def hexToBitList(hex : String) = {
    val list = hex.map { x =>
      x match {
        case '0' => List(0,0,0,0)
        case '1' => List(0,0,0,1)
        case '2' => List(0,0,1,0)
        case '3' => List(0,0,1,1)
        
        case '4' => List(0,1,0,0)
        case '5' => List(0,1,0,1)
        case '6' => List(0,1,1,0)
        case '7' => List(0,1,1,1)        

        case '8' => List(1,0,0,0)
        case '9' => List(1,0,0,1)
        case 'a' => List(1,0,1,0)
        case 'b' => List(1,0,1,1)
        
        case 'c' => List(1,1,0,0)
        case 'd' => List(1,1,0,1)
        case 'e' => List(1,1,1,0)
        case 'f' => List(1,1,1,1)        
        case _ => throw new BitVectorTheoryException("Non-hex characterin hex literal")
      }
    }
    list.flatten.toList
  }
    
  def parseLiteral(lit : String) = {
    val hexPattern = """#x([0-9A-Fa-f]+)""".r
    val binPattern = """#b([0-1]+)""".r
    val decPattern = """_ bv(\d+) (\d+)""".r
//    val bitPattern = """\(?fp (\S+) (\S+) ([^\s)]+)[)]*""".r    
//    val zeroPattern = "\\(?_ ([\\+\\-])zero (\\d+) (\\d+)\\)*".r
//    val infPattern = "\\(?_ ([\\+\\-])oo (\\d+) (\\d+)\\)*".r
//    val nanPattern = "\\(?_ NaN (\\d+) (\\d+)\\)*".r
    lit match {
      case hexPattern(p) => {
        val bits = hexToBitList(p)
        val sort = BVSort(bits.length)
        Leaf(BitVectorLiteral(bits, sort))
      }
      case binPattern(p) => {
        val bits = p.map(_.toInt - 48).toList
        val sort = BVSort(bits.length)
        Leaf(BitVectorLiteral(bits, sort))
      }
      
      case decPattern(const, sort) => {
        def toBinary(n:BigInt, bin: List[Int] = List.empty[Int]): List[Int] = {
          if(n/2 == 1) (1:: (n.toInt % 2) :: bin)
          else {
            val r = n % 2
            val q = n / 2
            toBinary(q, r.toInt::bin)
          }
        }        
        
        val constBits = if (const == "0") List(0) else toBinary(BigInt(const))
        println(const + " => " + constBits.mkString(""))
        val bvsort = BVSort(sort.toInt)
        val finalBits = if (constBits.length < sort.toInt)
          List.fill(sort.toInt - constBits.length)(0) ++ constBits
        else
          constBits
        Leaf(BitVectorLiteral(finalBits, bvsort))
      }
//      case "roundNearestTiesToEven" | "RNE" => RoundToNearestTiesToEven
//      case "roundNearestTiesToAway" | "RNA"  => RoundToNearestTiesToAway 
//      case "roundTowardPositive" | "RTP" => RoundToPositive
//      case "roundTowardNegative" | "RTN"  => RoundToNegative
//      case "roundTowardZero" | "RTZ" => RoundToZero      
//
//      case bitPattern(s1, s2, s3) => {
//        val sign = 
//          if (s1 == "#b0") 0
//          else if (s1 == "#b1") 1
//          else throw new Exception("Wrong sign bit: " + s1)
//        
//        val eBits = parseSymbol(s2).toList
//        val sBits = parseSymbol(s3).toList
//        val constFactory = new FPConstantFactory(sign, eBits, sBits)
//        val fpsort = FPSortFactory(List(eBits.length, sBits.length + 1))
//        Leaf(constFactory(List(fpsort)))
//      }
//      case zeroPattern(sign, eBits, sBits) => {
//        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
//        if (sign == "+") 
//          Leaf(FPPositiveZero(List(fpsort)))
//        else  
//          Leaf(FPNegativeZero(List(fpsort)))
//      }
//      case infPattern(sign, eBits, sBits) => {
//        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
//        if (sign == "+")
//          Leaf(FPPlusInfinity(List(fpsort)))
//        else
//          Leaf(FPMinusInfinity(List(fpsort)))
//      } 
//      case nanPattern(eBits, sBits) => {
//        val fpsort = FPSortFactory(List(eBits.toInt, sBits.toInt))
//        Leaf(FPNaN(List(fpsort)))        
//      }
      case _ => throw new BitVectorTheoryException("Unknown BV literal: " + lit)
    }
  }
 
  // Theory shouldn't be here
  case class BVVar(val name : String, val sort : BVSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = BitVectorTheory
  }
//  
//  object RMVar {
//    def apply(name : String) = {
//      new RMVar(name)
//    }
//    
//    def unapply(symbol : RMVar) : Option[String] = {
//        Some(symbol.name)
//    }  
//  }  
//  
//  class RMVar(val name : String) extends ConcreteFunctionSymbol {
//      val args = List()
//      val theory = FloatingPointTheory
//      val sort = RoundingModeSort
//    }  
//
//  // TODO: What to do with this
  val sorts : List[Sort] = List()
//
//  // TODO: How do we do this?
  val symbols = List() //: List[IndexedFunctionSymbol] = List(FPAdditionFactory.FPFunctionSymbol, FPSubtractionFactory.FPFunctionSymbol, FPEqualityFactory.FPPredicateSymbol)
//  
//  def isLiteral(symbol : ConcreteFunctionSymbol) = {
//    symbol match {
//      case l : FloatingPointLiteral => true
//      case rm : RoundingMode => true
//      case _ => false
//    }
//  }
  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
//      case FPVar(_, _) => false
//      case RMVar(_) => false
      case _ => true
    }
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case BVVar(_, _) => true
//      case FPVar(_, _) |
//           RMVar(_) => true
      case _ => false
    }
  }
//  
//  def getULP(fpValue : FloatingPointLiteral) = {
//    // TODO :  Distinguish normal and subnormal numbers  
//   
//    val newExp = intToBits(bitsToInt(fpValue.eBits) - fpValue.sort.sBitWidth, fpValue.sort.eBitWidth)
//    val newSignificand = List.fill(fpValue._sort.sBitWidth - 1)(0)
//    fp(0, newExp, newSignificand) (fpValue._sort)   
//  }
//  
  val SMTHeader = {
    "(set-logic QF_BV)" 
  }
//  
  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    val retval = 
      symbol match {
        case bvFunSym : BitVectorFunctionSymbol => {
          bvFunSym.getFactory match {
            case BVNotFactory => "bvnot"
            case bvzef : BVZeroExtendFactory => "(_ zero_extend " + bvzef.count + ")"
            case bvsef : BVSignExtendFactory => "(_ sign_extend " + bvsef.count + ")"
            case bvef : BVExtractFactory => "(_ extract " + bvef.startBit + " "  + bvef.endBit + ")"
            case BVAndFactory => "bvand"
            case BVAddFactory => "bvadd"
            case BVMulFactory => "bvmul"
            case BVDivFactory => "bvdiv"              
            case BVAshrFactory => "bvashr"  
            case BVOrFactory => "bvor"
            case BVXorFactory => "bvxor"  
            case BVConcatFactory => "concat"
            case BVConstantFactory(bits) => {
              bvFunSym.sort match {
                case BVSort(bitCount) => {
                  val bitString = bits.mkString("")
                  val extraZeroes = bitCount - bitString.length
                  "#b" + ("0"*extraZeroes) + bits.mkString("")   
                }
              }
            }
          }
        }
        
        // TODO: Signed or unsigned arithmetic!
        case bvPredSym : BitVectorPredicateSymbol => {
          bvPredSym.getFactory match {
            case BVEqualityFactory => "="
            case BVLessThanOrEqualFactory => "bvsle"
            case BVLessThanFactory => "bvslt"
          }
        }
        case BVVar(name, _) => name
        case _ => throw new BitVectorTheoryException("Not handled: " + symbol)
      }
    //println(symbol + " ----> " + retval)
    retval
  } 
//    symbol match {
//      case RoundToZero => "RTZ"
//      case RoundToPositive => "RTP"
//      case RoundToNegative => "RTN"
//      case RoundToNearestTiesToAway => "RNA"
//      case RoundToNearestTiesToEven => "RNE"
//      case RoundingModeEquality => "="
//      case fpFunSym : FloatingPointFunctionSymbol => {      
//        fpFunSym.getFactory match {
//          case FPPositiveZero => "(_ +zero " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
//          case FPNegativeZero => "(_ -zero " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
//          case FPPlusInfinity => "(_ +oo " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
//          case FPMinusInfinity => "(_ -oo " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
//          case FPNaN => "(_ NaN " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"
//          case FPAdditionFactory => "fp.add"
//          case FPSubstractionFactory => "fp.sub"
//          case FPMultiplicationFactory => "fp.mul"
//          case FPDivisionFactory => "fp.div"
//          case FPNegateFactory => "fp.neg"
//          case FPToFPFactory => "(_ to_fp " + fpFunSym.sort.eBitWidth + " " + fpFunSym.sort.sBitWidth + ")"         
//          case FPConstantFactory(sign, eBits, sBits) => {
//            val eDiff = eBits.length - fpFunSym.sort.eBitWidth
//            val ebits = if (eDiff >= 0)
//                          eBits.take(fpFunSym.sort.eBitWidth)
//                        else
//                          eBits.head :: List.fill(-eDiff)(0) ++ eBits.tail
//            val sDiff = sBits.length - fpFunSym.sort.sBitWidth + 1
//            val sbits = if (sDiff >= 0)
//                          sBits.take(fpFunSym.sort.sBitWidth)
//                        else
//                          sBits ++ List.fill(-sDiff)(0) 
//            
//            "(fp #b" + sign + " #b" + ebits.mkString("") + " #b" + sbits.mkString("") + ")" 
//          }
//          case str => throw new Exception("Unsupported FP symbol: " + str)
//        }
//      }
//      case fpPredSym : FloatingPointPredicateSymbol => {
//        fpPredSym.getFactory match {
//          case FPEqualityFactory => "fp.eq"
//          case FPLessThanOrEqualFactory => "fp.leq"
//          case FPLessThanFactory => "fp.lt"
//          case FPGreaterThanOrEqualFactory => "fp.geq"
//          case FPGreaterThanFactory => "fp.gt"
//          case str => throw new Exception("Unsupported FP symbol: " + str)
//        }
//      }
//      case uppsat.theory.FloatingPointTheory.RMVar(name) => name
//      case FPVar(name, _) => name
//      case other => throw new FloatingPointTheoryException("Unknown symbol: " + symbol)      
//    }
//  }
//  
//  
//  
  def sortToSMTLib(sort : ConcreteSort)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case BVSort(b) => "(_ BitVec " + b + ")"
//      case FPSort(e, s) => "(_ FloatingPoint " + e + " " + s + ")"
//      case RoundingModeSort => "RoundingMode"
      case _ => throw new BitVectorTheoryException("Not handled: " + sort)
    }
  }
//  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
//      case FPVar(name, _) => "(declare-fun " + name + " () " + toSMTLib(sym.sort) + ")"
      case _ => throw new BitVectorTheoryException("Not handled: " + sym)
    }
 }
}
