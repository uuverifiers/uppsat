

// TODO: We have to make sure precision is kept upwards, i.e. if a symbol has children with precision (d, f)_{i=0->n} then precision must be (max(d_i), max(f_i))

// TODO: Remember down casting and up casting loses precision

package uppsat.approximation



import uppsat.theory.BitVectorTheory._
import uppsat.theory.RealTheory._

import uppsat.theory.FixPointTheory
import uppsat.theory.FixPointTheory._
import uppsat.theory.FixPointTheory.FXSortFactory.FXSort
import uppsat.theory.FloatingPointTheory._
import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap.Path
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntTuplePrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.ModelReconstructor
import uppsat.ast.AST
import uppsat.ast._
import uppsat.solver.Z3Solver
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory._
import uppsat.globalOptions
import uppsat.precision.IntTuplePrecisionOrdering
import uppsat.theory.RealTheory.RealConstant
import uppsat.theory.RealTheory.RealSort



trait FPABVCore extends ApproximationCore {
   type Precision = (Int, Int) // (DecimalBits, FractionalBits)
   val precisionOrdering = new IntTuplePrecisionOrdering((4,3), (11,53))
   val inputTheory = FloatingPointTheory
   val outputTheory = FixPointTheory
}
//
trait FPABVCodec extends FPABVCore with ApproximationCodec {
//  // Encodes a node by scaling its sort based on precision and calling
//  // cast to ensure sortedness.
  var fpToFXMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()
//  
  

//  
  def cast(ast : AST, target : ConcreteSort) : AST = {
    (ast.symbol.sort, target) match {
//      case (FXLit : FixPointLiteral, fpsort : FPSort) => {
//        // TODO: (Peter) Assuming positive integers
//        val iValue = FXLit.bits.foldRight((0,1))((a,b) => (b._1 + a*b._2, b._2*2))._1
//        floatToAST(iValue.toFloat, fpsort)
//      }
//      case (FXVar : FXVar, fpsort : FPSort) => {
//        throw new Exception("This is hard...")
//      }
//      case (f : FloatingPointLiteral, _) =>
//        AST(f.getFactory(target), ast.label, List())
      
      case (RealSort, FXSort(decW, fracW)) => {
        ast.symbol match {
          case realValue : RealNumeral => {
            throw new Exception("mmmh!")
          }
          case realValue : RealDecimal => {
            val (sign, eBits, sBits) = floatToBits((realValue.num / realValue.denom).toFloat)
            
           val bits = sBits
           val (decimalWidth, fractionalWidth) = (decW, fracW)
           val decimalBits = 
             if (bits.length < decimalWidth)
               List.fill(decimalWidth - bits.length)(0) ++ bits
             else if (bits.length > decimalWidth)
               bits.drop(bits.length - decimalWidth)
             else
               bits
             bits.take(decimalWidth) 
           val fractionalBits = List.fill(fractionalWidth)(0)
           
           val sort = FXSort(decimalWidth, fractionalWidth)
           val symbol = FX(decimalBits, fractionalBits)(sort)
           
           println("£" + realValue)
           println("\t" + symbol)
           
           Leaf(symbol, ast.label)
            
            
          }
        }
      }
        
      case (FXSort(sourceDecimalBits, sourceFractionalBits), FXSort(targetDecimalBits, targetFractionalBits)) => {
        if (sourceDecimalBits != targetDecimalBits ||
            sourceFractionalBits != targetFractionalBits) {
            val c = FXToFXFactory(ast.symbol.sort)
            AST(c(target), List(ast))
        } else {
          ast
        }
      }
//        if (sourceBits < targetBits) {
//          val extraZeroes = targetBits - sourceBits
//          val newSort = FXSort(extraZeroes)
//          val zeroes = FixPointLiteral(List.fill(extraZeroes)(0), newSort)
//          val newAst = FXConcat(Leaf(zeroes), ast)
//          newAst.prettyPrint("....")
//          newAst
//        } else if (sourceBits > targetBits) {
//          FXExtract(sourceBits - targetBits, targetBits - 1, ast)
//        } else {
//          ast
//        }
//      }
      case sym => {
        println("cast(" + ast + ", " + target + ")")
        throw new Exception("don't cast me: " + ast.symbol.sort.getClass + ", " + target)
      }
    }
  }
//  
//  
//  
  
  def floatToFixPoint(sign : Int, eBits : List[Int], sBits : List[Int], fxsort : FXSort) = {
    val exp = ebitsToInt(eBits)
    
    
    val FXSort(integralWidth, fractionalWidth) = fxsort
    
    // Position indicates the number of bits in the integral part of the number 
    val position = exp + 1
   
    val (prependedBits, newPosition) = 
      if (position - integralWidth < 0) {
       (List.fill(integralWidth - position)(0) ++ (1 :: sBits), integralWidth) 
      } else {
        (1 :: sBits, position)
      }
    
    
    
    val appendedBits =
      if (integralWidth + fractionalWidth > prependedBits.length)
        prependedBits ++ List.fill(integralWidth + fractionalWidth - prependedBits.length)(0)
      else
        prependedBits
        
    // TODO: No sign bit?
    val iBits = appendedBits.drop(newPosition - integralWidth).take(integralWidth)
    val fBits = appendedBits.drop(newPosition).take(fractionalWidth)
    
    
    val (newiBits, newfBits) = 
      if (sign == 1) {
        // Do some 2-complements magic over iBits ++ fBits
        throw new Exception("negative floating point literal")
      } else {
        (iBits, fBits)
      }
    println(sign)
    println(eBits)
    println(sBits)
    println(fxsort)
    
    
    println("exp: " + exp)
    println("position: "+ position)
    println("newPosition: "+ newPosition)
    println("prepBits: " + prependedBits)
    println("appendedBits: " + appendedBits)
    println("iBits: " + iBits)
    println("fBits: " + fBits)
    FixPointLiteral(newiBits, newfBits, fxsort)    
    
  }
  
  def encodeNode(ast : AST, children : List[AST], precision : (Int, Int)) : AST = {
    println("encodeNode(" + ast + ")")
    val newSort = FXSortFactory(List(precision._1, precision._2))
      ast.symbol match {
      
      case fpVar : FPVar => {        
        if (!fpToFXMap.contains(fpVar) || fpToFXMap(fpVar).sort != newSort) {
          fpToFXMap += (fpVar ->  new FXVar(fpVar.name, newSort))
        }
        
        println("FPVAR: " + fpToFXMap(fpVar) + " (" + precision + ")")
        println("fpToFXMap(fpVar).sort: " + fpToFXMap(fpVar).sort)
        println("\t" + newSort)
        val symbol = fpToFXMap(fpVar)
        println("Symbol.sort: " + symbol.sort)
        val leaf = Leaf(fpToFXMap(fpVar), ast.label)
        println("Leaf.symbol.sort: " + leaf.symbol.sort)
        leaf.prettyPrint("leaf: ")
        leaf
      }
      
      
      case fpLit : FloatingPointLiteral => {
        fpLit.getFactory match {
           case FPConstantFactory(sign, eBits,  sBits) => {
             val fxSymbol = floatToFixPoint(sign, eBits, sBits, newSort)
             println("$" + fpLit)
             println("\t" + fxSymbol)
          
             Leaf(fxSymbol, ast.label)
           }
        }
      }
      
      
      // TODO: (Aleks) We drop the RoundingModeSorts, but how are they reintroduced in the final model?
      case fpSym : FloatingPointFunctionSymbol => {
        println("£" + fpSym)
        
        var newChildren = 
          for (c <- children if c.symbol.sort != RoundingModeSort) yield
            cast(c, newSort)
        var label = ast.label
        val newSymbol = fpSym.getFactory match {
          case FPNegateFactory   => FXNotFactory(newSort)
          case FPAdditionFactory => FXAddFactory(newSort)
          case FPSubstractionFactory => throw new Exception("Not handled: FP Substraction")
          case FPMultiplicationFactory => FXMulFactory(newSort)
          case FPDivisionFactory => FXMulFactory(newSort)
          
          case FPToFPFactory => val r = newChildren(0).symbol
                                label = newChildren(0).label
                                newChildren = newChildren(0).children
                                r
                                
          case _ => throw new Exception(fpSym + " unsupported")
        }
        
        
        AST(newSymbol, label, newChildren)
      }
      
      case fpPred : FloatingPointPredicateSymbol => {
        val newChildren =
          for (c <- children if c.symbol.sort != RoundingModeSort) yield
            cast(c, newSort)

        val newSymbol = fpPred.getFactory match {
          case FPEqualityFactory => FXEqualityFactory(newSort)
          case FPLessThanFactory => FXLessThanFactory(newSort)
          case FPLessThanOrEqualFactory => FXLessThanOrEqualFactory(newSort)
          case FPGreaterThanFactory => throw new Exception("Not handled: FP GreaterThan")
          case FPGreaterThanOrEqualFactory => throw new Exception("Not handled: FP GreaterThanOrEqual")
          case _ => throw new Exception(fpPred + " unsupported")
        }

        AST(newSymbol, ast.label, newChildren)
      }
      
      case rm : RoundingMode => rm
      
      case realValue : RealNumeral => throw new Exception("RealNumeral")
      case rv : RealDecimal => {
        val (sign, eBits, sBits) = floatToBits((rv.num / rv.denom).toFloat)
        val fxSymbol = floatToFixPoint(sign, eBits, sBits, newSort)
       println("$" + rv)
       println("\t" + fxSymbol)
    
       Leaf(fxSymbol, ast.label)        
        
      }
      
      case _ => AST(ast.symbol, ast.label, children) 
    }
  }
  // 101.011
  // 1.01011 = 2
  
  // sbits = [1.110] 
  // ebits = 2
  // float -> smt-float
  def FixPointToFloatAST(decimalBits : List[Int], fractionalBits : List[Int], fpsort : FPSort) : AST = {

    val signBit = decimalBits.head
    if (signBit == 1)
      throw new Exception("2-completemtn!")
    
    val FPSort(eBits, sBits) = fpsort
    
    val position = decimalBits.length - 1
    val allBits = decimalBits.tail ++ fractionalBits
    
    // Remove the return
    val leadingZeroes = allBits.takeWhile(_ == 0).length
    if (allBits.dropWhile(_ == 0).isEmpty) {
      if (signBit == 0)
        return Leaf(FPPositiveZero(fpsort))
      else
        return Leaf(FPNegativeZero(fpsort))
    }
    
    val actualBits = allBits.dropWhile(_ == 0).tail // Dropping implicit one
    
    val exp = position - leadingZeroes - 1
    
        
    // BIAS
    import scala.BigInt._
    val biasedExp = exp + 2.pow(eBits - 1).toInt - 1 
    val expBits = biasedExp.toBinaryString.map(_ - 48).toList
    
    // BIAS: Ask Christoph
    val exponent =
      if (expBits.length < eBits) {
        (List.fill(eBits - expBits.length)(0)) ++ expBits
      } else if (expBits.length > eBits) {
        // TODO: Maybe just set to max?
        expBits.drop(expBits.length - eBits)
      } else {
        expBits
      }
    
    // -1 for implicit one
    val mantissa =  
      if (actualBits.length < sBits - 1) {
        actualBits ++ List.fill(sBits - 1 - actualBits.length)(0) 
      } else if (actualBits.length > sBits - 1) {
        actualBits.take(sBits - 1)
      } else {
        actualBits
      }
    
//    println("FIX")
//    println("decimalBits: " + decimalBits)
//    println("fractionalBits: " + fractionalBits)
//    println("exp: "+ exp)
//    println("biasedExp: " + biasedExp)
//    println("exponent: " + exponent)
//    println("fpsort: " + fpsort)
//    println("position: " + position)
//    println("allBits: " + allBits)
//    println("actualBits: " + actualBits)
//    println("expBits: " + expBits)

    val symbol = fp(signBit, exponent, mantissa)(fpsort)
    println("symbol: " + symbol)
    Leaf(symbol, List())
    
  }
  
  // Describes translation of smallfloat values into values of the original formula.  
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : (Int, Int)) = {
    (symbol.sort, value.symbol) match {      
      case (FPSort(e, s), bvl : BitVectorLiteral) => {
        val (decimalWidth, fractionalWidth) = p
        if (bvl.bits.length != decimalWidth + fractionalWidth) {
          println(symbol)
          value.prettyPrint("¬¬¬")
          println(p)
          throw new Exception("Wrong bit-width in decoding")
        }
        val decimalBits = bvl.bits.take(decimalWidth)
        val fractionalBits = bvl.bits.drop(decimalWidth)
        val ret = FixPointToFloatAST(decimalBits, fractionalBits, FPSort(e, s))
        println("&")
        println(symbol)
        println(value)
        println(p)
        println(ret)
        ret
      }
      case (FPSort(e, s), fxl : FixPointLiteral) => {
//        // TODO: (Aleks) How do we know that the float value here is correctly representing something of sort FPSort(e,s)
        FixPointToFloatAST(fxl.decimalBits, fxl.fractionalBits, FPSort(e, s))      
      }
      
      case (BooleanSort, _) => value
      case (RoundingModeSort, _) => value
      
      // TODO: Maybe we might have to cast floating points?
      case (FPSort(_, _), _) => value
      // TODO: (Peter) How can we be confident we haven#t
      case (RealSort, rv : RealDecimal) => value
      case (RealSort, rv : RealNumeral) => value
      
      case _ => {
        println(symbol.sort)
        println(value.symbol)
        throw new Exception("decodesymbolValue(" + symbol + ", " + value + ", " + p + ")")
      }
      //case _ => value
    }
  }

  def retrieveFromAppModel(ast : AST, appModel : Model) = {
    if (appModel.contains(ast)) {
      appModel(ast)
    } else if (ast.isVariable && fpToFXMap.contains(ast.symbol)) {
      appModel(Leaf(fpToFXMap(ast.symbol), List()))
    }
    else if ( ast.symbol.isInstanceOf[FPFunctionSymbol] && 
              ast.symbol.asInstanceOf[FPFunctionSymbol].getFactory == FPToFPFactory)
      ast
    else
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
    
  }
//    
  
  // In contrast to cast, this is working on scala-level, not in SMT
  def decodeValue(ast : AST, target : ConcreteSort) = {
    (ast.symbol, target) match {
      case (fpl : FloatingPointLiteral, fps : FPSort) => {
//        val castValue = cast(retrieveFromAppModel(ast.children(1), appModel), ast.symbol.sort)
//        val dv = decodeSymbolValue(ast.symbol, castValue, pmap(ast.label)) 
//        dv
        val float = fp(fpl.sign, fpl.eBits, fpl.sBits)(fps)
        Leaf(float)
      }
      
      case (rv : RealDecimal, fps : FPSort) => {
        implicit val sort = fps
        val (sign, eBits, sBits) = floatToBits((rv.num / rv.denom).toFloat)
        val float = fp(sign, eBits, sBits)
        Leaf(float)
      }
//      case (fxl : FixPointLiteral, fps : FPSort) => {
//        println("---")
//        // TODO: Assuming integers right now
//        val iValue = FXl.bits.foldRight((0,1))((a,b) => (b._1 + a*b._2, b._2*2))._1
//        println(iValue)
//        val float = FloatingPointTheory.floatToAST(iValue, fps)
//        float
//      }
//      case (sort1, sort2) if sort1 == sort2 => ast
      case (sort1, sort2) => {
        println("Could not decode")
        ast.prettyPrint
        println("TO: " + target)
        throw new Exception("Could not decode")
      }
    }
  }
  
  // decodes values associated with nodes in the formula.
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    
    val appValue = retrieveFromAppModel(ast, appModel) 
    
    val decodedValue : AST = ast.symbol match {
      case f : FPFunctionSymbol if f.getFactory == FPToFPFactory =>
        val castValue = decodeValue(retrieveFromAppModel(ast.children(1), appModel), ast.symbol.sort)
        val dv = decodeSymbolValue(ast.symbol, castValue, pmap(ast.label)) 
        dv
      case _ => 
        decodeSymbolValue(ast.symbol, appValue, pmap(ast.label)) 
    }
    
    if (decodedModel.contains(ast)){
      val existingValue = decodedModel(ast).symbol 
      if ( existingValue != decodedValue.symbol) {
        ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue.symbol)
      }
    } else {
      if (ast.isVariable)
        println(">> "+ ast.symbol + " " + decodedValue.symbol + " /" + appValue.symbol +"/")
      decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
}
//
trait FPABVRefinementStrategy extends FPABVCore with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, (1,1))

  }
}
//  
//  def relativeError(decoded : FloatingPointLiteral, precise : FloatingPointLiteral) : Double = {
//    (decoded.getFactory, precise.getFactory) match {
//      case (x, y) if (x == y) => 0.0 //Values are the same
//      case (FPPlusInfinity, _)    |
//           (_, FPPlusInfinity)    |
//           (FPMinusInfinity, _)   |
//           (_, FPMinusInfinity)   => Double.PositiveInfinity
//      case (x : FPConstantFactory, y : FPConstantFactory) => {
//        val a = bitsToDouble(decoded)
//        val b = bitsToDouble(precise)
//        Math.abs((a - b)/b)
//      }        
//      case _ => 0.0
//    }
//  } 

object FPABVApp extends FPABVCore 
                  with FPABVCodec
                  with EqualityAsAssignmentReconstructor
                  with FPABVRefinementStrategy {
}
