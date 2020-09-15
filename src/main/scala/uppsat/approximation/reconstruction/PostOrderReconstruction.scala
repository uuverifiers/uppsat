package uppsat.approximation.reconstruction

import uppsat.approximation.ModelReconstruction
import uppsat.approximation.toolbox.Toolbox
import uppsat.ModelEvaluator.Model
import uppsat.ModelEvaluator
import uppsat.ast.AST
import uppsat.globalOptions._

trait PostOrderReconstruction extends ModelReconstruction {
  //def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy

  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0) {
      val newChildren = for ( c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(s"${ast.symbol} ${ast.label} <- ${newValue.symbol}")

      candidateModel.set(ast, newValue)
      ast.ppWithModels("", decodedModel, candidateModel, false)
    }
    candidateModel
  }

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, reconstructNode)
    reconstructedModel
  }

  // Utility function
//  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
//    if (! candidateModel.contains(ast)) {
//      verbose(ast.symbol + " " + ast.label + " " + " <- " + decodedModel(ast).symbol)
//      candidateModel.set(ast, decodedModel(ast))
//    }
//    candidateModel(ast)
//  }
}
