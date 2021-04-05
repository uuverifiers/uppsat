package uppsat.approximation.reconstruction

import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation.ModelReconstruction
import uppsat.approximation.toolbox.Toolbox
import uppsat.ast.AST
import uppsat.globalOptions
import uppsat.globalOptions._

trait PostOrderReconstruction extends ModelReconstruction {
  def reconstructNode(decodedModel  : Model,
                      candidateModel : Model,
                      ast : AST) : Model = {
    val AST(symbol, label, children) = ast

    if (children.length > 0) {
      val newChildren = for (c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(s"${ast.symbol} ${ast.label} <- ${newValue.symbol}")

      candidateModel.set(ast, newValue)
      if (globalOptions.MODEL)
        ast.ppWithModels("", decodedModel, candidateModel, false)
    }
    candidateModel
  }

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast,
                                reconstructedModel,
                                decodedModel,
                                reconstructNode)
    reconstructedModel
  }
}
