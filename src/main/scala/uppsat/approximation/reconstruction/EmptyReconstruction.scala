package uppsat.approximation.reconstruction

import uppsat.approximation.ModelReconstruction
import uppsat.ModelEvaluator.Model
import uppsat.ast.AST
import uppsat.globalOptions._

trait EmptyReconstruction extends ModelReconstruction {
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    decodedModel
  }
}