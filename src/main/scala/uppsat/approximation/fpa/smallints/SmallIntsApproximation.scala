package uppsat.approximation.smallints

import uppsat.approximation._


import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.theory.FloatingPointTheory._
import uppsat.Timer
import uppsat.ModelEvaluator.Model
import uppsat.precision.PrecisionMap.Path
//import uppsat.Encoder.PathMap
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
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
import uppsat.approximation.refinement.UniformRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.reconstruction.PostOrderReconstruction
import uppsat.theory.IntegerTheory
import uppsat.theory.IntegerTheory._



trait SmallIntsContext extends ApproximationContext {
   type Precision = Int
   val MAX_PRECISION = 100
   val precisionOrdering = new IntPrecisionOrdering(2, MAX_PRECISION)
   val inputTheory = IntegerTheory
   val outputTheory = IntegerTheory
}

trait SmallIntsCodec extends SmallIntsContext with PostOrderCodec {
  def encodeNode(ast : AST, children : List[AST], precision : Int) : AST = {
    if (ast.symbol.sort == IntegerSort && precision < MAX_PRECISION) {
      ast.symbol match {
        case intVar : IntVar => Leaf(intVar, ast.label)
        case intLit : IntLiteral => Leaf(intLit, ast.label)
        case intFun : IntegerFunctionSymbol => {
          val oldAst = AST(ast.symbol, List(), children)             
          
          
          val newAst = IntegerTheory.intModulo(oldAst, IntegerTheory.IntLiteral(precision))
          val newSymbol = newAst.symbol
          val newLabel = ast.label
          val newChildren = newAst.children
          val ret = AST(newSymbol, newLabel, newChildren)
          ret          
        }
        case intPred : IntegerPredicateSymbol => AST(intPred, ast.label, children)
      }
    } else {
      AST(ast.symbol, ast.label, children)
    }
  }

  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    if (!decodedModel.contains(ast))
      decodedModel.set(ast, appModel(ast))
    decodedModel
  }
}


trait SmallIntsRefinementStrategy extends SmallIntsContext with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, 1)
  }
}

object SmallIntsApp extends SmallIntsContext 
                    with SmallIntsCodec
                    with EmptyReconstruction
                    with SmallIntsRefinementStrategy {
}

