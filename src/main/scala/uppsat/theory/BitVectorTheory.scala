// TODO (ptr): Add support for whole SMT-lib Bit-Vector theory.

package uppsat.theory

import uppsat.theory.BooleanTheory._
import uppsat.ast._
import uppsat.theory.BitVectorTheory.BVSortFactory.BVSort

object BitVectorTheory extends Theory {
  val name = "BVTheory"

  case class BitVectorTheoryException(msg : String)
      extends Exception("BitVector Theory Exception: " + msg)

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

  abstract class BitVectorSymbol
      extends IndexedFunctionSymbol
  abstract class BitVectorFunctionSymbol(val sort : BVSort)
      extends BitVectorSymbol
  abstract class BitVectorPredicateSymbol
      extends BitVectorSymbol
  abstract class FloatingPointConstantSymbol(override val sort : BVSort)
      extends BitVectorFunctionSymbol(sort)


  abstract class BVGenConstantFactory extends IndexedFunctionSymbolFactory {
    def getName(sort : BVSort) : String
  }

object BitVectorLiteral {
    def apply(bits : List[Int], sort : BVSort) : BitVectorLiteral = {
      val newFactory = new BVConstantFactory(bits)
      if (sort.bitWidth != bits.length) {
        val msg ="Creating literal with wrong sort? " + sort + ", " + bits
        throw new BitVectorTheoryException(msg)
      }
      newFactory(sort).asInstanceOf[BitVectorLiteral]
    }
}

  case class BitVectorLiteral(_sort : BVSort, getFactory : BVGenConstantFactory)
             extends FloatingPointConstantSymbol(_sort) {
    val name = getFactory getName sort
    val theory = BitVectorTheory
    val args = List()
    lazy val bits = getFactory.asInstanceOf[BVConstantFactory].bits
  }

  case class BVFunctionSymbol(val args : Seq[ConcreteSort],
                              _sort : BVSort,
                              val getFactory : BVFunctionSymbolFactory)
             extends BitVectorFunctionSymbol(_sort) {
    val theory = BitVectorTheory
    val name = getFactory.symbolName
  }

  case class BVPredicateSymbol(val argSort : ConcreteSort,
                               val getFactory : BVPredicateSymbolFactory)
      extends BitVectorPredicateSymbol {
    val theory = BitVectorTheory
    val name = getFactory.symbolName
    val sort = BooleanSort
    val args = List.fill(getFactory.bvArity)(argSort)
  }

  case class BVFunctionSymbolFactory(symbolName : String,
                                     fpArity : Int)
      extends IndexedFunctionSymbolFactory {
    val thisFactory = this

    val arity = 1 // Refers to the sorts
    def apply(sorts : ConcreteSort*) = {
      sorts.reverse.head match {
        case bvsort : BVSort => {
          val argSorts = sorts.take(sorts.length - 1).toList
          val args = argSorts
          BVFunctionSymbol(args, bvsort, this)
        }
        case _ =>
          throw new BitVectorTheoryException("Non-BV sort : " + sorts.head)
      }
    }
  }

  case class BVPredicateSymbolFactory(symbolName : String,
                                      bvArity : Int)
      extends IndexedFunctionSymbolFactory {
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {
      BVPredicateSymbol(sort.head, this)
    }
  }

  // TODO: Bitset instead of List[Int]
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
        case _ =>
          throw new BitVectorTheoryException("Non-BV sort : " + sort.head)
      }
    }
  }

  val BVNotFactory =
    new BVFunctionSymbolFactory("not", 1)
  val BVLessThanOrEqualFactory =
    new BVPredicateSymbolFactory("less-than-or-equal", 2)
  val BVLessThanFactory =
    new BVPredicateSymbolFactory("less-than", 2)
  val BVEqualityFactory =
    new BVPredicateSymbolFactory("equal", 2)

  object BVZeroExtendFactory {
    def apply(count : Int) = {
      new BVZeroExtendFactory(count)
    }
  }

  class BVZeroExtendFactory(val count : Int)
      extends BVFunctionSymbolFactory("zero_extend", 1)

  object BVSignExtendFactory {
    def apply(count : Int) = {
      new BVSignExtendFactory(count)
    }
  }

  class BVSignExtendFactory(val count : Int)
      extends BVFunctionSymbolFactory("sign_extend", 1) {
  }

  object BVExtractFactory {
    def apply(startBit : Int, endBit : Int) = {
      new BVExtractFactory(startBit, endBit)
    }
  }
  class BVExtractFactory(val startBit : Int, val endBit : Int)
      extends BVFunctionSymbolFactory("extract", 1) {
  }

  val BVAndFactory = new BVFunctionSymbolFactory("bvAnd", 2)

  val BVAddFactory = new BVFunctionSymbolFactory("bvAdd", 2)
  val BVMulFactory = new BVFunctionSymbolFactory("bvMul", 2)
  val BVDivFactory = new BVFunctionSymbolFactory("bvDiv", 2)
  val BVAshrFactory = new BVFunctionSymbolFactory("bvAshr", 2)


  val BVOrFactory = new BVFunctionSymbolFactory("bvOr", 2)
  val BVXorFactory = new BVFunctionSymbolFactory("bvXor", 2)
  val BVConcatFactory = new BVFunctionSymbolFactory("concat", 2)

  def bv(bitlist : List[Int])(implicit sort : BVSort) = {
    val factory = new BVConstantFactory(bitlist)
    factory(sort)
  }

  def genericOperation(left : AST,
                       right : AST,
                       factory : BVFunctionSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : BVSort, r : BVSort) => {
        if (l != r) {
          val msg = "BV-Operation of non-equal sorts: " + l + " & " + r
        throw new BitVectorTheoryException(msg)
        }
        val children : List[AST] = List(left, right)
        AST(factory(l, l, l), children)
      }
      case _ => {
        val msg =
          "BV-Operation of non-BitVector-point AST: " + left + " and " + right
        throw new BitVectorTheoryException(msg)
      }
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
      case _ => {
        val msg = "BV-Operation of non-BitVector-point AST: " + arg
        throw new BitVectorTheoryException(msg)
      }
    }
  }

  def bvConcat(left : AST, right : AST) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (BVSort(bits), BVSort(bits2)) => {
        val newSort = BVSort(bits + bits2)
        val newSymbol = BVConcatFactory(newSort)
        AST(newSymbol, List(left, right))
      }
      case _ => {
        val msg = "Concat of non-Bitvector children: " + left.symbol.sort +
          ", " + right.symbol.sort
        throw new BitVectorTheoryException(msg)
      }
    }
  }

  def bvNot(arg : AST) = {
    arg.symbol.sort match {
      case sort : BVSort => {
        val children : List[AST] = List(arg)
        AST(BVNotFactory(sort), children)
      }
      case _ => {
        val msg = "BV-Operation of non-BitVector-point AST: " + arg
        throw new BitVectorTheoryException(msg)
      }
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


  // TODO: Maybe this can be placed somewhere more generic?
  def genericPredicate(left : AST,
                       right : AST,
                       factory : BVPredicateSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : BVSort, r : BVSort) => {
        if (l != r) {
          val msg = "BV-Predicate of non-equal sorts: " + l + " & " + r
          throw new BitVectorTheoryException(msg)
        }
        val children : List[AST] = List(left, right)
        val fpeq = factory(l)
        AST(fpeq, children)
      }
      case _ => {
        val msg = "BV-Predicate of non-floating-point AST: " + left +
          " and " + right
        throw new BitVectorTheoryException(msg)
      }
    }
  }

  def bvEquality(left : AST, right : AST) =
    genericPredicate(left, right, BVEqualityFactory)

  def bvLessThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, BVLessThanOrEqualFactory)

  def bvLessThan(left : AST, right : AST) =
    genericPredicate(left, right, BVLessThanFactory)

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
        case _ =>
          throw new BitVectorTheoryException("Non-hex characterin hex literal")
      }
    }
    list.flatten.toList
  }

  def parseLiteral(lit : String) = {
    val hexPattern = """#x([0-9A-Fa-f]+)""".r
    val binPattern = """#b([0-1]+)""".r
    val decPattern = """_ bv(\d+) (\d+)""".r

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
      case _ => throw new BitVectorTheoryException("Unknown BV literal: " + lit)
    }
  }

  // Theory shouldn't be here
  case class BVVar(val name : String,
                   val sort : BVSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = BitVectorTheory
  }

  // TODO: What to do with this
  val sorts : List[Sort] = List()
  // TODO: How do we do this?
  val symbols = List()

  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case _ => true
    }
  }

  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case BVVar(_, _) => true
      case _ => false
    }
  }

  val SMTHeader = {
    "(set-logic QF_BV)"
  }

  def symbolToSMTLib(symbol : ConcreteFunctionSymbol)
                    (implicit translator :
                         Option[uppsat.solver.SMTTranslator] = None) = {
    val retval =
      symbol match {
        case bvFunSym : BitVectorFunctionSymbol => {
          bvFunSym.getFactory match {
            case BVNotFactory => "bvnot"
            case bvzef : BVZeroExtendFactory =>
              "(_ zero_extend " + bvzef.count + ")"
            case bvsef : BVSignExtendFactory =>
              "(_ sign_extend " + bvsef.count + ")"
            case bvef : BVExtractFactory =>
              "(_ extract " + bvef.startBit + " "  + bvef.endBit + ")"
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
    retval
  }

  def sortToSMTLib(sort : ConcreteSort)
                  (implicit translator
                       : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case BVSort(b) => "(_ BitVec " + b + ")"
      case _ => throw new BitVectorTheoryException("Not handled: " + sort)
    }
  }

  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case _ => throw new BitVectorTheoryException("Not handled: " + sym)
    }
  }
}
