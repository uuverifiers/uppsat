package uppsat.approximation.codec

import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.ast.AST
import uppsat.ast.AST.Label
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.precision.{PrecisionMap, PrecisionOrdering}

/** The EmptyCodec is used by the empty approximation. */
trait EmptyCodec extends Codec {
  case class EmptyCodecException(msg : String)
      extends Exception("Empty Codec Exception: " + msg)

  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) =
    throw new EmptyCodecException("Trying to encode formula in empty theory.")
  def decodeModel(ast : AST,
                  appModel : Model,
                  pmap : PrecisionMap[Precision]) =
  throw new EmptyCodecException("Trying to decode model in empty theory.")
}

