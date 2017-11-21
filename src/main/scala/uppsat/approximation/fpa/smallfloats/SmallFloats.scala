package uppsat.approximation.fpa.smallfloats

import uppsat.approximation._
import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.BooleanTheory.BooleanSort
import uppsat.Timer
import uppsat.ModelEvaluator.Model
import uppsat.precision.PrecisionMap.Path
//import uppsat.Encoder.PathMap
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.ModelEvaluator
import uppsat.ast.AST
import uppsat.ast._
import uppsat.solver.Z3Solver
import uppsat.solver.Z3OnlineSolver
import uppsat.theory.BooleanTheory.BoolTrue
import uppsat.theory.BooleanTheory.BoolFalse
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory.BooleanFunctionSymbol
import uppsat.theory.BooleanTheory.BooleanConstant
import uppsat.theory.BooleanTheory.BoolVar
import uppsat.ModelEvaluator.Model
import uppsat.solver.Z3OnlineException
import uppsat.solver.Z3OnlineSolver
import uppsat.globalOptions
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.ErrorBasedRefinementStrategy
import uppsat.approximation.refinement.UniformPGRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.reconstruction.PostOrderReconstruction

trait SmallFloatsCore extends ApproximationCore {
   type Precision = Int
   val precisionOrdering = new IntPrecisionOrdering(0,5)
   val inputTheory = FloatingPointTheory
   val outputTheory = FloatingPointTheory   
}

  /**
   * The core of the smallfloats approximation!
	 * Other approximations might add top level constraints over the domain rather than 
   * change the sorts of the formula itself.
	 */

trait SmallFloatsCodec extends SmallFloatsCore with PostOrderCodec {

  class SmallFloatsException(msg : String) extends Exception("SmallFloats: " + msg)
  
  /**
   * Scales sort of the AST node according to the precision p
	 *  
   * @param ast is the node whose sort will be scaled down.
   * @param p is the precision used to calculate the new sort.
   * 
   * @return sort scaled down according to p 
	 */
  def scaleSort(ast : AST, p : Int, encodedChildren : List[AST]) = {
    val AST(symbol, label, children) = ast
    val sort = symbol.sort
    symbol match {
      case _ : FloatingPointPredicateSymbol =>
        val childrenSorts = encodedChildren.filterNot(x => FloatingPointTheory.isLiteral(x.symbol)).map(_.symbol.sort) 
        childrenSorts.foldLeft(childrenSorts.head)(fpsortMaximum)
   
      case _ : FloatingPointFunctionSymbol =>
        val FPSort(eBitWidth, sBitWidth) = sort
        val eBits = 3 + ((eBitWidth - 3) * p)/precisionOrdering.maximalPrecision
        val sBits = 3 + ((sBitWidth - 3) * p)/precisionOrdering.maximalPrecision
        FPSort(eBits, sBits)
      
      case _ => sort 
    }
  }

  /**
   * Checks whether s1 greater than s2 (i.e. has more number of bits).
	 *  
   * @param s1 first sort.
   * @param ast second sort.
   * 
   * @return larger of the FPSorts in terms of bits, otherwise s1
	 */  
  def fpsortMaximum(s1 : ConcreteSort, s2 : ConcreteSort) : ConcreteSort = {
    (s1, s2) match {
      case (FPSort(eb1, sb1), FPSort(eb2, sb2)) => 
        if (eb1 + sb1 > eb2 + sb2) s1 else s2      
      case _ => s1 // Keep the accumulator
    }
  }
  
  /**
   * Creates a new AST casting to target .
	 *  
	 *  Creates a new AST identical to ast with the possible addition of a
	 *  casting node at the root if ast is not of sort target. If the ast is not
	 *  of a FPSort, it is returned as-is.
	 *  
   * @param ast The AST to be casted.
   * @param target The sort to which ast is casted.
   * 
   * @return ast if sort of ast is target, otherwise ast with a new root node which casts ast to target sort. 
	 */
  def cast(ast : AST, target : ConcreteSort) : AST = {
    val source = ast.symbol.sort
    source match {
      case FPSort(_, _) if source != target => {
        val cast = FPToFPFactory(source, target)
        val rtz = AST(RoundToZero, List(), List())
        AST(cast, List(), List(rtz, ast))
      }
      case _ => ast
    }
  }

  def encodeSymbol(sym : ConcreteFunctionSymbol, sort : ConcreteSort, encodedChildren : List[AST]) : ConcreteFunctionSymbol = {
    (sym, sort) match {
      case (_ : FloatingPointConstantSymbol, _) => sym
      case (fpSym : FloatingPointFunctionSymbol, fpsort : FPSort) =>
        val sorts = encodedChildren.map(_.symbol.sort) ++ List(fpsort) 
        fpSym(sorts : _*)
      case (fpPred : FloatingPointPredicateSymbol, _) =>
        val sorts = encodedChildren.map(_.symbol.sort) ++ List(BooleanSort) 
        fpPred(sorts : _*)
      case _ => sym
    }
  }

  /** Encodes a node by scaling its sort based on precision and calling cast to ensure sortedness.
   *  
   *  @param ast Node of ast to encode.
   *  @param precision Precision to encode
   *  
   *  @return ast encoded according to precision.
   */
  def encodeNode(ast : AST, encodedChildren : List[AST], precision : Int) : AST = {
    val sort = scaleSort(ast, precision, encodedChildren)
    val children = encodedChildren.map(cast(_, sort))
    val symbol = encodeSymbol(ast.symbol, sort, children)
    AST(symbol, ast.label, children)
  }
  
  /** Decodes an approximative model value back to full precision.
   *  
   *  @param symbol A symbol representing the full precision sort.
   *  @param value The value to be converted.
   *  @param p The precision to which value was encoded.
   *  
   *  @return value decoded to the sort of symbol if it was encoded by precision p.
   */  
  def decodeFPValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) : ConcreteFunctionSymbol = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), fp : FloatingPointLiteral) => {
        fp.getFactory match {
          case _ : FPSpecialValuesFactory => fp(FPSort(e, s))          
          case _ if !fp.eBits.contains(1) => {
            val sPrefix = fp.sBits.dropWhile(_ == 0)
            val eUnderflow = fp.sBits.length - sPrefix.length
            val sBits = sPrefix.tail ::: List.fill(s - sPrefix.length)(0)  
            val exp = - bias(fp.eBits.length) - eUnderflow
            val eBits = intToBits(biasExp(exp, e), e)                       
            FloatingPointLiteral(fp.sign, eBits, sBits, FPSort(e,s))
          }
          case _ => {
            val exp = unbiasExp(fp.eBits, fp.eBits.length)
            val eBits = intToBits(biasExp(exp, e), e)
            val missing = (s - 1) - fp.sBits.length
            val sBits = fp.sBits ::: List.fill(missing)(0)
            FloatingPointLiteral(fp.sign, eBits, sBits, FPSort(e, s))
          }
        }
      }      
      case _ => value.symbol
    }
  }
  
  // decodes values associated with nodes in the formula.
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val (appModel, pmap) = args
    
    // TEMPORARY TODO: (Aleks) FIX!
    val newAST = 
      if (ast.isVariable)    
        encodeNode(ast, List(), pmap(ast.label))
      else
        ast
    
    if (!appModel.contains(newAST))
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
    
    val decodedValue = decodeFPValue(ast.symbol, appModel(newAST), pmap(ast.label))
    
    if (!decodedModel.contains(ast))
      decodedModel.set(ast, Leaf(decodedValue))
    else {
      val existingValue = decodedModel(ast).symbol 
      if ( existingValue != decodedValue) {
        ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue)
      }
    } 
      
    decodedModel
  }
}


trait SmallFloatsRefinementStrategy extends SmallFloatsCore 
                                       with ErrorBasedRefinementStrategy
                                       with UniformPGRefinementStrategy{
  val topK = 10 // K 
  val fractionToRefine = 1.0//K_percentage
  val precisionIncrement = 1 // 20/100 = 1/5

  def satRefinePrecision( node : AST, pmap : PrecisionMap[Int]) : Int = {
    val p =  pmap(node.label)    
    val newP = (p + precisionIncrement) max p
    newP min pmap.precisionOrdering.maximalPrecision // TODO:  This check should be in the ordering somewhere?
  }
  
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
  
  def computeRelativeError ( ast : AST, decodedModel : Model, failedModel : Model) : Option[Double] = {
    (decodedModel(ast).symbol, failedModel(ast).symbol) match {
      case (aValue : FloatingPointLiteral, bValue : FloatingPointLiteral) => 
          Some(relativeError(aValue, bValue))
      case _ => None
    }
  }
  
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {
    val AST(symbol, label, children) = ast      
    symbol match {
      case literal : FloatingPointLiteral => accu      
      case fpfs : FloatingPointFunctionSymbol => {
        val Some(outErr) = computeRelativeError(ast, decodedModel, failedModel)
        val inErrors = children.map(computeRelativeError(_, decodedModel, failedModel)).collect{case Some(x) => x}
        val sumInErrors = inErrors.fold(0.0){(x,y) => x + y}
        val avgInErr = sumInErrors /  inErrors.length
        accu + (ast -> outErr / (1 + avgInErr))        
      }
      case _ => accu
    }
  }
  
  def relativeError(decoded : FloatingPointLiteral, precise : FloatingPointLiteral) : Double = {
    (decoded.getFactory, precise.getFactory) match {
      case (x, y) if (x == y) => 0.0 //Values are the same
      case (FPPlusInfinity, _)    |
           (_, FPPlusInfinity)    |
           (FPMinusInfinity, _)   |
           (_, FPMinusInfinity)   => Double.PositiveInfinity
      case (x : FPConstantFactory, y : FPConstantFactory) => {
        val a = bitsToDouble(decoded)
        val b = bitsToDouble(precise)
        Math.abs((a - b)/b)
      }        
      case _ => 0.0
    }
  } 
}

object IJCARSmallFloatsApp extends SmallFloatsCore 
                              with SmallFloatsCodec
                              with EqualityAsAssignmentReconstruction
                              with SmallFloatsRefinementStrategy                               

object IJCARSmallFloatsNodeByNodeApp extends SmallFloatsCore 
                                   with SmallFloatsCodec
                                   with PostOrderReconstruction
                                   with SmallFloatsRefinementStrategy
                              
                              
object IJCARSmallFloatsEmptyapp extends SmallFloatsCore 
                                   with SmallFloatsCodec
                                   with EmptyReconstruction
                                   with SmallFloatsRefinementStrategy

object FxPntSmallFloatsApp extends SmallFloatsCore 
                              with SmallFloatsCodec
                              with FixpointReconstruction
                              with SmallFloatsRefinementStrategy
                              
                              
