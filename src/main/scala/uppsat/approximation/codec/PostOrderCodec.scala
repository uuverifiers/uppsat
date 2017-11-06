package uppsat.approximation.codec

import uppsat.ast.AST
import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelEvaluator.Model
import uppsat.approximation._

trait PostOrderCodec extends Codec {
  def encodeNode(ast : AST, children : List[AST], precision : Precision) : AST 
  def decodeNode(args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST = { 
    val AST(symbol, label, children) = ast
    val newChildren =
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }
    encodeNode(ast, newChildren, pmap(ast.label))
  }

  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Precision]) : Model = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
}

