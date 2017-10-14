package uppsat.theory

import uppsat.theory.BooleanTheory._
import uppsat.ast._
import uppsat.theory.FixPointTheory.FXSortFactory.FXSort
case class FixPointTheoryException(msg : String) extends Exception("FixPoint Theory Exception: " + msg)

/**
 * Describes the Theory of Fixed Point
 * 
 * A fixed point number consists of a tuple with one "integral part" and one "fractional part".
 * Intuitively, a fixed point number (int, frac) = ([101], [011]) can be interpreted as the 
 * number 101.011).
 * 
 */
object FixPointTheory extends Theory {
  val name = "FixPointTheory"
    
  
  // 
  //  Sorts
  //
  object FXSortFactory extends IndexedSortFactory { 
    case class FXSort(integralWidth : Int, fractionalWidth : Int) extends IndexedSort {
      val name = "FixPoint (" + integralWidth + " " + fractionalWidth + ")"
      val theory = FixPointTheory
      val getFactory = FXSortFactory
      
      if (integralWidth < 0 || fractionalWidth < 0)
        throw new FixPointTheoryException("Negative bit-width: " + name)        
    }
  
    val arity = 1
    
    // TODO: (Peter) Do we want repeated arguments here as well?
    def apply(idx : Seq[BigInt]) = {
      val decWidth = idx(0).toInt
      val fracWidth = idx(1).toInt
      // TODO: Use HashTable to store and re-use
      FXSort(decWidth, fracWidth)
    }
  }

  
  //
  //  Symbols/Predicate-factories
  //
  abstract class FixPointSymbol extends IndexedFunctionSymbol
  abstract class FixPointFunctionSymbol(val sort : FXSort) extends FixPointSymbol
  abstract class FixPointPredicateSymbol extends FixPointSymbol
  abstract class FloatingPointConstantSymbol(override val sort : FXSort) extends FixPointFunctionSymbol(sort)
  abstract class FXGenConstantFactory extends IndexedFunctionSymbolFactory {
    def getName(sort : FXSort) : String
  }
  abstract class FXGenFXToFXFactory extends IndexedFunctionSymbolFactory {
    def getName(sort : FXSort) : String
  }  

  case class FXFunctionSymbol(val args : Seq[ConcreteSort], _sort : FXSort, val getFactory : FXFunctionSymbolFactory) 
             extends FixPointFunctionSymbol(_sort) {   
    val theory = FixPointTheory
    val name = getFactory symbolName
  }
  
  case class FXPredicateSymbol( val argSort : ConcreteSort, val getFactory : FXPredicateSymbolFactory) extends FixPointPredicateSymbol {   
    val theory = FixPointTheory    
    val name = getFactory symbolName
    val sort = BooleanSort
    val args = List.fill(getFactory FXArity)(argSort)
  }
  
  case class FXFunctionSymbolFactory(symbolName : String, fpArity : Int) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    val arity = 1 // Refers to the sorts
    def apply(sorts : ConcreteSort*) = {
      sorts.reverse.head match {
        case fxsort : FXSort => {      
          val argSorts = sorts.take(sorts.length - 1).toList
          val args = argSorts
          FXFunctionSymbol(args, fxsort, this)
        }
        case _ =>  throw new Exception("Non-FX sort : " + sorts.head)
      }  
    }
  }

  case class FXPredicateSymbolFactory(symbolName : String, FXArity : Int) extends IndexedFunctionSymbolFactory {
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {      
      FXPredicateSymbol(sort.head, this)  
    }
  }
  
  //
  //  FX To FX 
  //
  
  object FXToFXSymbol {
    def apply(sourceSort : FXSort, targetSort : FXSort) : FXToFXSymbol = {
      val newFactory = new FXToFXFactory(targetSort)

      newFactory(sourceSort).asInstanceOf[FXToFXSymbol]
    }
  }

  case class FXToFXSymbol(_sort : FXSort, getFactory : FXGenFXToFXFactory)
             extends FixPointFunctionSymbol(_sort) {
    val name = getFactory getName sort
    val theory = FixPointTheory
    val args = List()
    lazy val sourceSort = getFactory.asInstanceOf[FXToFXFactory].sourceSort
  }
  
  case class FXToFXFactory(sourceSort : Sort) extends FXGenFXToFXFactory {
    val thisFactory = this
    
    def getName(sort : FXSort) = {
      "fx-to-fx" 
    }
    
    val arity = 1 // Refers to the sorts
    override def apply(sort : ConcreteSort*) = {
      sort.head match {
        case fxsort : FXSort =>
          FXToFXSymbol(fxsort, this)
        case _ =>  throw new FixPointTheoryException("Non-FX sort : " + sort.head)
      }  
    }     
  }  
  
  //
  //  Literal
  //
  
  object FixPointLiteral {
    def apply(integralBits : List[Int], fractionalBits : List[Int], sort : FXSort) : FixPointLiteral = {
      val newFactory = new FXConstantFactory(integralBits, fractionalBits)
      if (sort.integralWidth != integralBits.length || sort.fractionalWidth != fractionalBits.length)
        throw new FixPointTheoryException("Creating literal with wrong sort? " + sort + ", " + integralBits + "." + fractionalBits)

      newFactory(sort).asInstanceOf[FixPointLiteral]
    }
  }
  
  case class FixPointLiteral(_sort : FXSort, getFactory : FXGenConstantFactory)
             extends FloatingPointConstantSymbol(_sort) {
    val name = getFactory getName sort
    val theory = FixPointTheory
    val args = List()
    lazy val integralBits = getFactory.asInstanceOf[FXConstantFactory].integralBits
    lazy val fractionalBits = getFactory.asInstanceOf[FXConstantFactory].fractionalBits
  }  
  

  //
  // Constant
  //
  
  // TODO: Integers instead of List[Int]
  case class FXConstantFactory(integralBits : List[Int], fractionalBits : List[Int]) extends FXGenConstantFactory {
    val thisFactory = this

    def getName(sort : FXSort) = {
      integralBits.mkString("") + "." + fractionalBits.mkString("")
    }
    
    val arity = 2 // Refers to the sorts
    // TODO: Should arity be 1 here?
    override def apply(sort : ConcreteSort*) = {
      sort.head match {
        case fxsort : FXSort =>
          FixPointLiteral(fxsort, this)
        case _ =>  throw new FixPointTheoryException("Non-FX sort : " + sort.head)
      }  
    }    
  }

  //
  //  Fixed Point Fucntions/Predicates
  
  val FXNotFactory = new FXFunctionSymbolFactory("not", 1)
  val FXLessThanOrEqualFactory = new FXPredicateSymbolFactory("less-than-or-equal", 2)
  val FXLessThanFactory = new FXPredicateSymbolFactory("less-than", 2)
  val FXEqualityFactory = new FXPredicateSymbolFactory("equal", 2)
  object FXZeroExtendFactory {
    def apply(count : Int) = {
      new FXZeroExtendFactory(count)
    }
  }
  
  class FXZeroExtendFactory(val count : Int) extends FXFunctionSymbolFactory("zero_extend", 1)
  
  object FXSignExtendFactory {
    def apply(count : Int) = {
      new FXSignExtendFactory(count)
    }
  }
  
  class FXSignExtendFactory(val count : Int) extends FXFunctionSymbolFactory("sign_extend", 1) {

  }
  
  object FXExtractFactory {
    def apply(startBit : Int, endBit : Int) = {
      new FXExtractFactory(startBit, endBit)
    }
  }
  class FXExtractFactory(val startBit : Int, val endBit : Int) extends FXFunctionSymbolFactory("extract", 1) {
    
  }
  val FXAndFactory = new FXFunctionSymbolFactory("FXAnd", 2)
  val FXAddFactory = new FXFunctionSymbolFactory("FXAdd", 2)
  val FXSubFactory = new FXFunctionSymbolFactory("FXSub", 2)
  val FXMulFactory = new FXFunctionSymbolFactory("FXMul", 2)
  val FXDivFactory = new FXFunctionSymbolFactory("FXDiv", 2)
  val FXOrFactory = new FXFunctionSymbolFactory("FXOr", 2)
  val FXXorFactory = new FXFunctionSymbolFactory("FXXor", 2)  

  //
  // Interface
  // 
  def FX(integralBits : List[Int], fractionalBits : List[Int])(implicit sort : FXSort) = {
    val factory = new FXConstantFactory(integralBits, fractionalBits)
    factory(sort)
  } 

  def genericOperation(left : AST, right : AST, factory : FXFunctionSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FXSort, r : FXSort) => {
        if (l != r)
          throw new Exception("FX-Operation of non-equal sorts: " + l + " & " + r)
        val children : List[AST] = List(left, right)
        AST(factory(l, l, l), children)
      }
      case _ => throw new Exception("FX-Operation of non-FixPoint-point AST: " + left + " and " + right)
    }  
  }

  
  def FXNot(arg : AST) = {
    arg.symbol.sort match {
      case sort : FXSort => {
        val children : List[AST] = List(arg)
        AST(FXNotFactory(sort), children)
      }
      case _ => throw new Exception("FX-Operation of non-FixPoint-point AST: " + arg)
    }
  }

  def FXOr(left : AST, right : AST) = 
    genericOperation(left, right, FXOrFactory)  

  def FXXor(left : AST, right : AST) = 
  genericOperation(left, right, FXXorFactory)  
  
  def FXAnd(left : AST, right : AST) = 
    genericOperation(left, right, FXAndFactory)  


  def FXAdd(left : AST, right : AST) = 
    genericOperation(left, right, FXAddFactory)  

  def FXSub(left : AST, right : AST) = 
    genericOperation(left, right, FXSubFactory)  
      
    
  def FXMul(left : AST, right : AST) = 
    genericOperation(left, right, FXMulFactory)  

  def FXDiv(left : AST, right : AST) = 
    genericOperation(left, right, FXDivFactory)  
        
  // TODO: Maybe this can be placed somewhere more generic?
  def genericPredicate(left : AST, right : AST, factory : FXPredicateSymbolFactory) = {
    (left.symbol.sort, right.symbol.sort) match {
      case (l : FXSort, r : FXSort) => {
        if (l != r)
          throw new Exception("FX-Predicate of non-equal sorts: " + l + " & " + r)
        val children : List[AST] = List(left, right)
        val fpeq = factory(l)
        AST(fpeq, children)
      }
      case _ => throw new Exception("FX-Predicate of non-floating-point AST: " + left + " and " + right)
    }  
  }

  def FXEquality(left : AST, right : AST) = 
    genericPredicate(left, right, FXEqualityFactory)

  def FXLessThanOrEqual(left : AST, right : AST) =
    genericPredicate(left, right, FXLessThanOrEqualFactory)
    
  def FXLessThan(left : AST, right : AST) =
    genericPredicate(left, right, FXLessThanFactory)
    
    
  // Since there are no FixPoint symbols in SMT,
  // we will always parse bit-vectors.
  def parseLiteral(lit : String) = {
    uppsat.theory.BitVectorTheory.parseLiteral(lit)    
  }
 
  // Theory shouldn't be here
  case class FXVar(val name : String, val sort : FXSort) extends ConcreteFunctionSymbol {
    val args = List()
    val theory = FixPointTheory
  }
  // TODO: What to do with this
  val sorts : List[Sort] = List()

  // TODO: How do we do this?
  val symbols = List() //: List[IndexedFunctionSymbol] = List(FPAdditionFactory.FPFunctionSymbol, FPSubtractionFactory.FPFunctionSymbol, FPEqualityFactory.FPPredicateSymbol)

  def isDefinedLiteral(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FXVar(_, _) => false
      case _ => true
    }
  }
  
  def isVariable(symbol : ConcreteFunctionSymbol) = {
    symbol match {
      case FXVar(_, _) => true
      case _ => false
    }
  }

  val SMTHeader = ""

  //
  //  Auxilliary Functions
  //
  def genFxToFxName(sd : Int, sf : Int, td : Int, tf : Int) = {
    "fx-to-fx-" + sd + "-" + sf + "-to-" + td + "-" + tf
  }
  def genFxToFx(sd : Int, sf : Int, td : Int, tf : Int) = {
    // SMT-lib argument name is "fx"
    // Start by fixing the integral bits:
    val firstStep = 
      if (sd < td) {
        // Pad with zeroes
        val constant = "#b" + ("0"*(td-sd))
        "(concat " + constant + " fx)"
      } else if (sd > td) {
        throw new Exception("Downcasting FX")
      } else {
        "fx"
      }
    
    val secondStep = 
      if (sf < tf) {
        // Pad with zeroes
        val constant = "#b" + ("0"*(tf-sf))
        "(concat 	" + firstStep + " " + constant + ")"
      } else if (sf > tf) {
        throw new Exception("Downcasting FX")
      } else {
        firstStep
      }        
    
    val funName = genFxToFxName(sd, sf, td, tf)
    "(define-fun " + funName + " ((fx (_ BitVec " + (sd + sf) + "))) (_ BitVec " + (td + tf) + ") " + secondStep + ")"
  }   
  
  def genFxMulName(d : Int, f : Int) = {
    "fx.mul-" + d + "-" + f
  }
  
  def genFxMul(d : Int, f : Int) = {
    val name = genFxMulName(d, f)
    val sort = "(_ BitVec " + (d + f) + ")"
    val pad = "(_ sign_extend " + f + ")"
    val extract = "(_ extract " + (d + 2*f - 1) + " " + (f) + ")"
    "(define-fun " + name + " ((bv1 " + sort + ") (bv2 " + sort + ")) " + sort + " (" + extract + " (bvmul (" + pad + " bv1) (" + pad + " bv2))))"
  }
  
  def genFxDivName(d : Int, f : Int) = {
    "fx.div-" + d + "-" + f
  }
  
  def genFxDiv(d : Int, f : Int) = {
    val name = genFxDivName(d, f)
    val sort = "(_ BitVec " + (d + f) + ")"
    val prep = "(_ sign_extend " + f + ")"
    val appBits = "#b" + "0"*f
    val extract = "(_ extract " + (d + f - 1) + " 0)"
    "(define-fun " + name + " ((bv1 " + sort + ") (bv2 " + sort + ")) " + sort + " (" + extract + " (bvudiv (concat bv1 " + appBits + ") (" + prep + " bv2))))"
  }  
  
  
def symbolToSMTLib(symbol : ConcreteFunctionSymbol)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = { 
    symbol match {
      case fxFunSym : FixPointFunctionSymbol => {
        fxFunSym.getFactory match {
          case FXNotFactory => "bvnot"
          case fxzef : FXZeroExtendFactory => "(_ zero_extend " + fxzef.count + ")"
          case fxsef : FXSignExtendFactory => "(_ sign_extend " + fxsef.count + ")"
          case fxef : FXExtractFactory => "(_ extract " + fxef.startBit + " "  + fxef.endBit + ")"
          case FXAndFactory => "bvand"
          case FXAddFactory => "bvadd"
          case FXSubFactory => "bvsub"
          case FXMulFactory => {
            if (translator.isDefined) {
              val FXSort(d, f) = fxFunSym.sort
              
              if (!translator.get.smtDefs.contains(genFxMul(d, f)))
                translator.get.smtDefs += genFxMul(d, f)
              println(">>>" + genFxMul(d, f))
              genFxMulName(d, f)                
            } else {
              "fxmul"
            }
          }
          
          case FXDivFactory => {
            if (translator.isDefined) {
              val FXSort(d, f) = fxFunSym.sort
              
              if (!translator.get.smtDefs.contains(genFxDiv(d, f)))
                translator.get.smtDefs += genFxDiv(d, f)
              println(">>>" + genFxDiv(d, f))
              genFxDivName(d, f)                
            } else {
              "fxdiv"
            }
          }
                        
          case FXOrFactory => "bvor"
          case FXXorFactory => "bvxor"  
          case FXToFXFactory(sourceSort) => {
            if (translator.isDefined) {
              val FXSort(sd, sf) = sourceSort
              val FXSort(td, tf) = fxFunSym.sort
              
              if (!translator.get.smtDefs.contains(genFxToFx(sd, sf, td, tf)))
                translator.get.smtDefs += genFxToFx(sd, sf, td, tf) 
              genFxToFxName(sd, sf, td, tf)                
            } else {
              "fx-to-fx"
            }
          }
          case FXConstantFactory(integralBits, fractionalBits) => {
            fxFunSym.sort match {
              case FXSort(integralWidth, fractionalWidth) => {
                val bitString = integralBits.mkString("") + fractionalBits.mkString("")
                if (bitString.length != integralWidth + fractionalWidth) {
                  println("bitString: " + bitString)
                  println("(" + integralWidth + ", " + fractionalWidth + ")")
                  throw new Exception("FX constant with wrong sort")
                }
                "#b" + bitString   
              }
            }
          }
        }
      }
      
      // TODO: Signed or unsigned arithmetic!
      case fxPredSym : FixPointPredicateSymbol => {
        fxPredSym.getFactory match {
          case FXEqualityFactory => "="
          case FXLessThanOrEqualFactory => "bvsle"
          case FXLessThanFactory => "bvslt"
        }
      }
      case FXVar(name, _) => name
      case _ => throw new FixPointTheoryException("Not handled: " + symbol)
    }
  } 

  def sortToSMTLib(sort : ConcreteSort)(implicit translator : Option[uppsat.solver.SMTTranslator] = None) = {
    sort match {
      case FXSort(integralWidth, fractionalWidth) => "(_ BitVec " + (integralWidth + fractionalWidth) + ")"
      case _ => throw new FixPointTheoryException("Not handled: " + sort)
    }
  }
  
  def declarationToSMTLib(sym : ConcreteFunctionSymbol) : String = {
    sym match {
      case FXVar(name, _) => "(declare-fun " + name + " () " + sortToSMTLib(sym.sort) + ")"
      case _ => throw new FixPointTheoryException("Not handled: " + sym)
    }
 }
}