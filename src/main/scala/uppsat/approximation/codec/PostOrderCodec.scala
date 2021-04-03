package uppsat.approximation.codec

import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.ast.AST
import uppsat.ast.AST.Label
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.precision.{PrecisionMap, PrecisionOrdering}

/** The PostOrderCodec allows for describing codec which moves over a formula in
  * a post-order fashion.
  *
  */
trait PostOrderCodec extends Codec {
  /** Encode a single node.
    *
    */
  def encodeNode(symbol : ConcreteFunctionSymbol,
                 label : Label,
                 children : List[AST],
                 precision : Precision) : AST

  /** Decode a single model value.
    *
    */
  def decodeNode(args : (Model, PrecisionMap[Precision]),
                 decodedModel : Model, ast : AST) : Model
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST = { 
    val AST(symbol, label, children) = ast
    val newChildren =
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }
    encodeNode(symbol, ast.label, newChildren, pmap(ast.label))
  }

  def decodeModel(ast : AST,
                  appModel : Model,
                  pmap : PrecisionMap[Precision]) : Model = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
}

