package uppsat.approximation

import uppsat.theory.FloatingPointTheory._
import uppsat.Timer
import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.ModelReconstructor
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
import uppsat.ModelReconstructor.Model
import uppsat.solver.Z3OnlineException
import uppsat.solver.Z3OnlineSolver
import uppsat.globalOptions
import uppsat.theory.RealTheory._
import uppsat.theory.RealTheory

trait FPARealCore extends ApproximationCore {
   type Precision = Int
   val precisionOrdering = new IntPrecisionOrdering(0,0)
   val inputTheory = FloatingPointTheory
   val outputTheory = RealTheory
}

trait FPARealCodec extends FPARealCore with ApproximationCodec {
  // Encodes a node by scaling its sort based on precision and calling
  // cast to ensure sortedness.
  var fpToRealMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()
  
  def cast(ast : AST, target : ConcreteSort  ) : AST = {
    ast.symbol match {
      case f : FloatingPointLiteral =>
        AST(f.getFactory (target), ast.label, List())
      case _ => ast
    }
  }
  
  
  
  def encodeNode(ast : AST, children : List[AST], precision : Int) : AST = {
      ast.symbol match {
      
      case fpVar : FPVar => {        
        if (!fpToRealMap.contains(fpVar)) {
          fpToRealMap = fpToRealMap + (fpVar ->  new RealVar(fpVar.name))
        }
        Leaf(fpToRealMap(fpVar), ast.label)
      }
      
      
      case fpLit : FloatingPointLiteral => {
        fpLit.getFactory match {
           case FPConstantFactory(sign, ebits,  sbits) => {
             val exp = (sbits.length + 1 - (ebitsToInt(ebits)))
             
             val num = if (exp > 0) {
                 bitsToInt((1::sbits) ++ (List.fill(exp)(0)))
             } else {
               bitsToInt(1::sbits)
             }
             
             val denom = if (exp > 0) {
               BigInt(1)
             } else {
               BigInt(1) << (- exp)
             }
              
             Leaf(RealDecimal(num, denom), ast.label)
           }
        }
      }
      
      
      case fpSym : FloatingPointFunctionSymbol => {
        var newChildren = if (children.head.symbol.sort == RoundingModeSort) children.tail 
                          else children
        
        var label = ast.label
        val newSymbol = fpSym.getFactory match {
          case FPNegateFactory   => RealNegation
          case FPAdditionFactory => RealAddition
          case FPSubstractionFactory => RealSubstraction
          case FPMultiplicationFactory => RealMultiplication
          case FPDivisionFactory => RealDivision
          
          case FPToFPFactory => val r = newChildren(0).symbol
                                label = newChildren(0).label
                                newChildren = newChildren(0).children
                                r
                                
          case _ => throw new Exception(fpSym + " unsupported")
        }
        
        
        AST(newSymbol, label, newChildren)
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
        AST(newSymbol, ast.label, children)
      }
      
      
      
      case _ => {
        AST(ast.symbol, ast.label, children) 
      }
    }
  }
  
  // Describes translation of smallfloat values into values of the original formula.  
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), RealZero) => {
          Leaf(FPPositiveZero(FPSort(e, s)))       
      }   
      case (FPSort(e, s), realValue : RealDecimal) => {
          //TODO: Refine this to be more sens
          val value = (BigDecimal(realValue.num) / BigDecimal(realValue.denom)).toDouble
          floatToAST(value.toFloat, FPSort(e,s))       
      }   
      case (FPSort(e, s), realValue : RealNumeral) => {
          //TODO: Refine this to be more sens
          val value = (BigDecimal(realValue.num)).toDouble
          floatToAST(value.toFloat, FPSort(e,s))       
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
    
    val decodedValue = ast.symbol match {
      case f : FPFunctionSymbol if f.getFactory == FPToFPFactory =>
        val castValue = cast(retrieveFromAppModel(ast.children(1), appModel), ast.symbol.sort)
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

trait FPARealRefinementStrategy extends FPARealCore with ErrorBasedRefinementStrategy {
  val topK = 10 // K 
  val fractionToRefine = 1.0//K_percentage
  val precisionIncrement = 1 // 20/100 = 1/5

  def satRefinePrecision( node : AST, pmap : PrecisionMap[Int]) : Int = {
    val p =  pmap(node.label)    
    val newP = (p + precisionIncrement) max p
    precisionOrdering.min(newP, pmap.precisionOrdering.maximalPrecision) // TODO:  This check should be in the ordering somewhere?
  }
  
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
  
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {
    val AST(symbol, label, children) = ast      
    var err = 0.0
    
    symbol match {
      case literal : FloatingPointLiteral => ()
      case fpfs : FloatingPointFunctionSymbol =>
        (decodedModel(ast).symbol, failedModel(ast).symbol)  match {
        case (approximate : FloatingPointLiteral, exact : FloatingPointLiteral) => {
          val outErr = relativeError(approximate, exact)
          
          var sumDescError = 0.0
          var numFPArgs = 0
          
          for (c <- children) {
            val a = decodedModel(c)
            val b = failedModel(c)
            
            (a.symbol, b.symbol) match {
              case (aS : FloatingPointLiteral, bS: FloatingPointLiteral) => {
                sumDescError +=  relativeError(aS, bS)
                numFPArgs += 1
              }                                                                 
              case  _ => ()
            }
          }
          val inErr = sumDescError / numFPArgs
          
          if (numFPArgs == 0) 
            err = outErr
          else
            err = outErr / inErr
        }
        case _ => ()
      }
      case _ => ()
    }
    
    
    if (err == 0.0)
      accu
    else
      accu + (ast -> err)
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

object FPARealApp extends FPARealCore 
                  with FPARealCodec
                  with EqualityAsAssignmentReconstructor
                  with FPARealRefinementStrategy {
}
