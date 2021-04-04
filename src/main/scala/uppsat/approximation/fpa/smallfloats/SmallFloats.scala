package uppsat.approximation.fpa.smallfloats

import uppsat.ModelEvaluator.Model

import uppsat.approximation._
import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.
  {ErrorBasedRefinementStrategy, UniformPGRefinementStrategy}
import uppsat.approximation.reconstruction.
  {EmptyReconstruction, PostOrderReconstruction}
import uppsat.ast.AST.Label
import uppsat.ast._
import uppsat.precision.{IntPrecisionOrdering, PrecisionMap}
import uppsat.theory.BooleanTheory.BooleanSort
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.FloatingPointTheory

/** The context of the smallfloats approximation.
  *
	* Other approximations might add top level constraints over the domain
  * rather than change the sorts of the formula itself.
  */
trait SmallFloatsContext extends ApproximationContext {
   type Precision = Int
   val precisionOrdering = new IntPrecisionOrdering(0,5)
   val inputTheory = FloatingPointTheory
   val outputTheory = FloatingPointTheory
}

/** The codec of the SmallFloats approximation. */
trait SmallFloatsCodec extends SmallFloatsContext with PostOrderCodec {

  class SmallFloatsException(msg : String)
      extends Exception("SmallFloats: " + msg)

  /** Scales sort of the AST node according to the precision p.
	 *
   * @param ast is the node whose sort will be scaled down.
   * @param p is the precision used to calculate the new sort.
   *
   * @return sort scaled down according to p
	 */
  def scaleSort(symbol : ConcreteFunctionSymbol,
                p : Int,
                encodedChildren : List[AST]) = {
    val sort = symbol.sort
    symbol match {
      case _ : FloatingPointPredicateSymbol =>
        val childrenSorts = encodedChildren.filterNot{
          x => FloatingPointTheory.isLiteral(x.symbol)
        }.map(_.symbol.sort)
        childrenSorts.foldLeft(childrenSorts.head)(fpsortMaximum)

      case _ : FloatingPointFunctionSymbol =>
        val FPSort(eBitWidth, sBitWidth) = sort
        val eBits = 3 + ((eBitWidth - 3) * p)/precisionOrdering.maximalPrecision
        val sBits = 3 + ((sBitWidth - 3) * p)/precisionOrdering.maximalPrecision
        FPSort(eBits, sBits)

      case _ => sort
    }
  }

  /** Checks whether s1 greater than s2 (i.e. has more number of bits).
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

  /** Creates a new AST casting to target.
	 *
	 *  Creates a new AST identical to ast with the possible addition of a
	 *  casting node at the root if ast is not of sort target. If the ast is not
	 *  of a FPSort, it is returned as-is.
	 *
   * @param ast The AST to be casted.
   * @param target The sort to which ast is casted.
   *
   * @return ast if sort of ast is target, otherwise ast with a new root node
   * which casts ast to target sort.
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

  def encodeSymbol(sym : ConcreteFunctionSymbol,
                   sort : ConcreteSort,
                   encodedChildren : List[AST]) : ConcreteFunctionSymbol = {
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

  /** Encodes a node by scaling its sort based on precision and calling cast to
    * ensure sortedness.
    *
    *  @param ast Node of ast to encode.
    *  @param precision Precision to encode
    *
    *  @return ast encoded according to precision.
    */
  def encodeNode(symbol : ConcreteFunctionSymbol,
                 label : Label,
                 encodedChildren : List[AST],
                 precision : Int) : AST = {
    val sort = scaleSort(symbol, precision, encodedChildren)
    val newChildren = encodedChildren.map(cast(_, sort))
    val newSymbol = encodeSymbol(symbol, sort, newChildren)
    AST(newSymbol, label, newChildren)
  }

  def decodeSubnormalFP(fp : FloatingPointLiteral,
                        sort : ConcreteSort) : ConcreteFunctionSymbol = {
    val FPSort(e, s) = sort
    val sPrefix = fp.sBits.dropWhile(_ == 0)
    val eUnderflow = fp.sBits.length - sPrefix.length
    val sBits = sPrefix.tail ::: List.fill(s - sPrefix.length)(0)
    val exp = - bias(fp.eBits.length) - eUnderflow
    val eBits = intToBits(biasExp(exp, e), e)
    FloatingPointLiteral(fp.sign, eBits, sBits, FPSort(e,s))
  }

  def isSubnormal(fp: FloatingPointLiteral) : Boolean = {
     !fp.eBits.contains(1)
  }

  def decodeNormalFP(fp : FloatingPointLiteral,
                     sort : ConcreteSort) : ConcreteFunctionSymbol = {
    val FPSort(e, s) = sort
    val exp = unbiasExp(fp.eBits, fp.eBits.length)
    val eBits = intToBits(biasExp(exp, e), e)
    val missing = (s - 1) - fp.sBits.length
    val sBits = fp.sBits ::: List.fill(missing)(0)
    FloatingPointLiteral(fp.sign, eBits, sBits, FPSort(e, s))
  }

  /** Decodes an approximative model value back to full precision.
    *
    *  @param symbol A symbol representing the full precision sort.
    *  @param value The value to be converted.
    *  @param p The precision to which value was encoded.
    *
    *  @return value decoded to the sort of symbol if it was encoded by precision
    *  p.
   */
  def decodeFPValue(symbol : ConcreteFunctionSymbol,
                    value : AST,
                    p : Int) : ConcreteFunctionSymbol = {
    value.symbol match {
      case fp : FloatingPointLiteral =>
        fp.getFactory match {
          case _ : FPSpecialValuesFactory => fp(symbol.sort)
          case _ if isSubnormal(fp) => decodeSubnormalFP(fp, symbol.sort)
          case _ => decodeNormalFP(fp, symbol.sort)
        }
      case _ => value.symbol
    }
  }

  def decodeNode(args : (Model, PrecisionMap[Precision]),
                 decodedModel : Model,
                 ast : AST) : Model = {
    val (appModel, pmap) = args

    // TEMPORARY TODO: (Aleks) FIX!
    val newAST =
      if (ast.isVariable)
        encodeNode(ast.symbol, ast.label, List(), pmap(ast.label))
      else
        ast

    if (!appModel.contains(newAST)) {
      val msg = "Node " + ast + " does not have a value in \n" +
        appModel.subexprValuation + "\n" + appModel.variableValuation
      throw new SmallFloatsException(msg)
    }

    val decodedValue =
      decodeFPValue(ast.symbol, appModel(newAST), pmap(ast.label))

    if (!decodedModel.contains(ast))
      decodedModel.set(ast, Leaf(decodedValue))
    else {
      val existingValue = decodedModel(ast).symbol
      if ( existingValue != decodedValue) {
        ast.prettyPrint("\t")
        val msg = "Decoding the model results in different values for the " +
          "same entry : \n" + existingValue + " \n" + decodedValue
        throw new SmallFloatsException(msg)
      }
    }

    decodedModel
  }
}

trait SmallFloatsPGRefinementStrategy extends UniformPGRefinementStrategy {
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
}

trait SmallFloatsMGRefinementStrategy extends SmallFloatsContext
                                       with ErrorBasedRefinementStrategy {
  val topK = 10 // K
  val fractionToRefine = 1.0 //K_percentage
  val precisionIncrement = 1 // 20/100 = 1/5

  def satRefinePrecision(node : AST, pmap : PrecisionMap[Int]) : Int = {
    val p =  pmap(node.label)
    val newP = (p + precisionIncrement) max p
    // TODO:  This check should be in the ordering somewhere?
    // AZ: pMap Already does this check in the map call. We should cut this.
    newP min pmap.pOrd.maximalPrecision 
  }

  def computeRelativeError(ast : AST,
                           decodedModel : Model,
                           failedModel : Model) : Option[Double] = {
    (decodedModel(ast).symbol, failedModel(ast).symbol) match {
      case (aValue : FloatingPointLiteral, bValue : FloatingPointLiteral) =>
          Some(relativeError(aValue, bValue))
      case _ => None
    }
  }

  def nodeError(decodedModel : Model)
               (failedModel : Model)
               (accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {
    val AST(symbol, label, children) = ast
    symbol match {
      case literal : FloatingPointLiteral => accu
      case fpfs : FloatingPointFunctionSymbol => {
        val Some(outErr) = computeRelativeError(ast, decodedModel, failedModel)
        val inErrors = children.map{
          computeRelativeError(_, decodedModel, failedModel)
        }.collect{case Some(x) => x}
        val sumInErrors = inErrors.fold(0.0){(x,y) => x + y}
        val avgInErr = sumInErrors /  inErrors.length
        accu + (ast -> outErr / (1 + avgInErr))
      }
      case _ => accu
    }
  }

  def relativeError(decoded : FloatingPointLiteral,
                    precise : FloatingPointLiteral) : Double = {
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

object IJCARSmallFloatsApp extends SmallFloatsContext
    with SmallFloatsCodec
    with EqualityAsAssignmentReconstruction
    with SmallFloatsMGRefinementStrategy
    with SmallFloatsPGRefinementStrategy

object IJCARSmallFloatsNodeByNodeApp extends SmallFloatsContext
    with SmallFloatsCodec
    with PostOrderReconstruction
    with SmallFloatsMGRefinementStrategy
    with SmallFloatsPGRefinementStrategy

object IJCARSmallFloatsEmptyapp extends SmallFloatsContext
    with SmallFloatsCodec
    with EmptyReconstruction
    with SmallFloatsMGRefinementStrategy
    with SmallFloatsPGRefinementStrategy

object FxPntSmallFloatsApp extends SmallFloatsContext
    with SmallFloatsCodec
    with FixpointReconstruction
    with SmallFloatsMGRefinementStrategy
    with SmallFloatsPGRefinementStrategy
