package uppsat.approximation.reconstruction

import uppsat.globalOptions._
import uppsat.ModelEvaluator.Model
import uppsat.approximation.ModelReconstruction
import uppsat.ast.AST

/** Empty reconstruction, just passes on decoded model */
trait EmptyReconstruction extends ModelReconstruction {

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    decodedModel
  }
}
