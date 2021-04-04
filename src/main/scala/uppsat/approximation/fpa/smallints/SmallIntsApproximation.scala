// TODO (ptr): Comment better and make tutorial how to achieve? Find benchmark
// where it works well and incorporate.

package uppsat.approximation.smallints

import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.approximation.codec._
import uppsat.approximation.refinement.UniformRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.precision.{IntPrecisionOrdering, PrecisionMap}
import uppsat.ast.{AST, ConcreteFunctionSymbol, Leaf}
import uppsat.ast.AST.Label
import uppsat.theory.IntegerTheory
import uppsat.theory.IntegerTheory._


/** SmallInts is an example approximation. */
trait SmallIntsContext extends ApproximationContext {
   type Precision = Int
   val MAX_PRECISION = 100
   val precisionOrdering = new IntPrecisionOrdering(2, MAX_PRECISION)
   val inputTheory = IntegerTheory
   val outputTheory = IntegerTheory
}

/** SmallInts is an example approximation. */
trait SmallIntsCodec extends SmallIntsContext with PostOrderCodec {

  def encodeNodeModulo(symbol : ConcreteFunctionSymbol,
                       label : Label,
                       children : List[AST],
                       precision : Int) : AST = {
      symbol match {
        case _ : IntVar | _ : IntLiteral => AST(symbol, label, children)
        case _: IntegerFunctionSymbol => {
          val newSymbol = IntegerTheory.IntModulo
          val newChildren =
            List(AST(symbol, List(), children),
                 Leaf(IntegerTheory.IntLiteral(precision)))
          AST(newSymbol, label, newChildren)
        }
        case _ => AST(symbol, label, children)
      }
  }

  def encodeNodeLessThanOrEqual(symbol : ConcreteFunctionSymbol,
                                label : Label,
                                children : List[AST],
                                precision : Int) : AST = {
        symbol match {
          case _ : IntVar | _ : IntLiteral => AST(symbol, label, children)
          case _: IntegerFunctionSymbol => {
            val oldAST = AST(symbol, List(), children)
            val const = Leaf(IntegerTheory.IntLiteral(precision))
            val condAST = IntegerTheory.intLessThanOrEqual(oldAST, const)
            val newAST = IntegerTheory.intITE(condAST, oldAST, const)
            AST(newAST.symbol, label, newAST.children)
          }
          case _ => AST(symbol, label, children)
        }
  }

  def encodeNode(symbol : ConcreteFunctionSymbol,
                 label : Label,
                 children : List[AST],
                 precision : Int) : AST =
    encodeNodeLessThanOrEqual(symbol, label, children, precision)

  def decodeNode(args : (Model, PrecisionMap[Precision]),
                 decodedModel : Model,
                 ast : AST) : Model = {
    if (!decodedModel.contains(ast))
      decodedModel.set(ast, args._1(ast))
    decodedModel
  }
}

trait SmallIntsRefinementStrategy extends SmallIntsContext
    with UniformRefinementStrategy {

  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, 1)
  }
}

object SmallIntsApp extends SmallIntsContext
                    with SmallIntsCodec
                    with EmptyReconstruction
                    with SmallIntsRefinementStrategy {
}

