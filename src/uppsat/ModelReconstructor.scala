package uppsat

import uppsat.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model

object ModelReconstructor {
  type Model = Map[Path, AST]  
}

class ModelReconstructor[T](approximation : Approximation[T]) {
  var constructedModel = None : Option[Model]
  var updatedPrecisionMap = None : Option[PrecisionMap[T]]
 
  // TODO: Do we want the type partialModel / partialPrecisionMap
  def reconstructAST(ast : AST, path : Path, appModel : Model, sourceToEncoding : PathMap, pmap : PrecisionMap[T]) : Model = {
    ast match {
      case leafAST @ Leaf(symbol) => {
        if (symbol.theory.isDefinedLiteral(symbol)) {
          // TODO: Maybe we only to path -> leafAST here...
          Map(path -> leafAST)
        } else {
          Map(path -> appModel(sourceToEncoding(path)))          
        }
      }
      
      case intAST @ AST(symbol, children) => {
        (for ((c,i) <- children zip children.indices) yield {
          reconstructAST(c, i :: path, appModel, sourceToEncoding, pmap).toMap
        }).foldLeft(List(path -> appModel(sourceToEncoding(path))).toMap)(_ ++ _)
      }
      
      
    }
  }
  
  // Given an original formula (ast), and a model over an approximate formula (model).
  // created using a PathMap (sourceToEncoding), translate it to a model over the original formula
  def reconstruct(ast : AST, model : Model, sourceToEncoding : PathMap, pmap : PrecisionMap[T]) : Model = {
    reconstructAST(ast, List(), model, sourceToEncoding, pmap)
  }
  
  //TODO: move validation here
}