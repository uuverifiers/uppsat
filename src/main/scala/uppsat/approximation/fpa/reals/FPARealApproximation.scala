package uppsat.approximation.fpa.reals

import uppsat.approximation._
import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.theory.FloatingPointTheory._
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
import uppsat.theory.RealTheory._
import uppsat.theory.RealTheory
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.UniformRefinementStrategy

trait FPARealCore extends ApproximationCore {
   type Precision = Int
   val precisionOrdering = new IntPrecisionOrdering(0, 1)
   val inputTheory = FloatingPointTheory
   val outputTheory = RealTheory
}

trait FPARealCodec extends FPARealCore with PostOrderCodec {
  // Encodes a node by scaling its sort based on precision and calling
  // cast to ensure sortedness.
  var fpToRealMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()


  def cast(ast : AST, newSort : ConcreteSort) = {
    if (ast.symbol.sort == newSort)
      ast
    else {
      newSort match {
        case FPSort(s,e) =>
          AST(RealToFPFactory(newSort), List(), List(ast))
        case RealSort =>
          AST(FPToRealFactory(ast.symbol.sort), List(), List(ast))
      }
    }
  }

  // Encode FP by precision value:
  // 0 - Replace FP constraints with corresponding Real constraints
  // 1 - Introduce \epsilon > 0  as buffer in constraints to avoid rounding disrupting model reconstruction
  // 3 - No encoding, retain FP constraints
  import BigInt._;

  def encodeNode(ast : AST, children : List[AST], precision : Int) : AST = {
    val (newAst, newChildren) =
      precision match {
        case precisionOrdering.maximalPrecision =>
          (ast, children)

        case 0 =>
          ast.symbol match {
            case fpVar : FPVar => {
              if (!fpToRealMap.contains(fpVar)) {
                fpToRealMap = fpToRealMap + (fpVar ->  new RealVar(fpVar.name))
              }
              (Leaf(fpToRealMap(fpVar), ast.label), children)
            }

            case fpLit : FloatingPointLiteral => {
              fpLit.getFactory match {
                case FPNegativeZero => {
                  (Leaf(RealNumeral(0), ast.label), children)
                }
                case FPPositiveZero => {
                  (Leaf(RealNumeral(0), ast.label), children)
                }
                case FPPlusInfinity => {
                  (Leaf(RealNumeral(2.pow(53) + 1), ast.label), children) // TODO: fix magic constants
                }

                case FPMinusInfinity => {
                  (Leaf(RealNumeral(-(2.pow(53) + 1)), ast.label), children) // TODO: fix magic constants
                }

                case FPConstantFactory(sign, ebits,  sbits) => {
                  val exp = (sbits.length + 1 - (ebitsToInt(ebits)))

                  val num = if (exp > 0) {
                    BigInt(bitsToInt((1::sbits) ++ (List.fill(exp)(0))))
                  } else { 
                    BigInt(bitsToInt(1::sbits))
                  }

                  val denom = if (exp > 0) {
                    BigInt(1)
                  } else {
                    BigInt(1) << (- exp)
                  }

                  (Leaf(RealDecimal(num, denom), ast.label), children)
                }
              }
            }

            case fpSym : FloatingPointFunctionSymbol => {
              var nChildren = if (children.head.symbol.sort == RoundingModeSort) children.tail
                                else children

              var nLabel = ast.label
              val newSymbol = fpSym.getFactory match {
                case FPNegateFactory   => RealNegation
                case FPAdditionFactory => RealAddition
                case FPSubstractionFactory => RealSubstraction
                case FPMultiplicationFactory => RealMultiplication
                case FPDivisionFactory => RealDivision
                case FPToFPFactory => val r = nChildren(0).symbol
                  nLabel = nChildren(0).label
                  nChildren = nChildren(0).children
                  r
                case _ => throw new Exception(fpSym + " unsupported")
              }
              (AST(newSymbol, nLabel, nChildren), nChildren)
            }
            case fpPred : FloatingPointPredicateSymbol => {
              val newSymbol = fpPred.getFactory match {
                case FPEqualityFactory => RealEquality
                case FPLessThanFactory => RealLT
                case FPLessThanOrEqualFactory => RealLEQ
                case FPGreaterThanFactory => RealGT
                case FPGreaterThanOrEqualFactory => RealGEQ
                case _ => throw new Exception(fpPred + " unsupported")
              }
              (AST(newSymbol, ast.label, children), children)
            }
            case _ => {
              (AST(ast.symbol, ast.label, children), children)
            }
          }

        case _  =>
          (ast, children)
      }


    val sortedChildren =
      for (i <- newChildren.indices)
      yield
          cast(newChildren(i), newAst.symbol.args(i))

    AST(newAst.symbol, newAst.label, sortedChildren.toList)
  }

  // Describes translation of smallfloat values into values of the original formula.  
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), RealZero) => {
          Leaf(FPPositiveZero(FPSort(e, s)))       
      }

      // TODO:  unify these two cases 
      case ( fpsort : FPSort, realValue : RealDecimal) => {
        val value = (BigDecimal(realValue.num) / BigDecimal(realValue.denom))
        if (value.abs >= BigDecimal(2.pow(53) + 1))
          if (value > 0)
            (Leaf(FPPlusInfinity(fpsort)))
          else
            (Leaf(FPMinusInfinity(fpsort)))
          else
            fpToAST(value.toDouble, fpsort)
      }

      case ( fpsort : FPSort, realValue : RealNumeral) => {
        val value = (BigDecimal(realValue.num) / BigDecimal(realValue.denom))
        if (value.abs >= BigDecimal(2.pow(53) + 1))
          if (value > 0)
            (Leaf(FPPlusInfinity(fpsort)))
          else
            (Leaf(FPMinusInfinity(fpsort)))
          else
            fpToAST(value.toDouble, fpsort)
      }
      
      case _ => value
    }
  }

  def retrieveFromAppModel(ast : AST, appModel : Model) = {
    if (appModel.contains(ast)) {
      appModel(ast)
    } else if (ast.isVariable && fpToRealMap.contains(ast.symbol)) {
      appModel(Leaf(fpToRealMap(ast.symbol), List()))
    }
    else if ( ast.symbol.isInstanceOf[FPFunctionSymbol] &&
              ast.symbol.asInstanceOf[FPFunctionSymbol].getFactory == FPToFPFactory)
      ast
    else
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
  }

  // decodes values associated with nodes in the formula.
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2

    val appValue = retrieveFromAppModel(ast, appModel)

    val decodedValue = decodeSymbolValue(ast.symbol, appValue, pmap(ast.label))

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


trait FPARealRefinementStrategy extends FPARealCore with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, 1)

  }
}

object FPARealApp extends FPARealCore 
                  with FPARealCodec
                  with EqualityAsAssignmentReconstruction
                  with FPARealRefinementStrategy {
}

object FxPntFPARealApp extends FPARealCore 
                  with FPARealCodec
                  with FixpointReconstruction
                  with FPARealRefinementStrategy {
}
