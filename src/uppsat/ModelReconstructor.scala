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
  // TODO: should we do this?
  var failed = false
  
  def validateAST(ast : AST, path : Path, appModel : Model, exactModel : Map[Path, AST], sourceToEncoding : PathMap) : Option[Model] = {
    // Which approximate ast does the original ast correspond to?
    // sourceToEncoding has the answer
    
    val approximateValue = appModel(sourceToEncoding(path))
    
    val exactDescValues = ast.children.indices.map(x => exactModel(sourceToEncoding(x :: path))).toList
    val newAST = AST(ast.symbol, exactDescValues)
    val translator = new SMTTranslator(approximation.outputTheory)
    val astSMT = translator.translateNoAssert(newAST)
    val result = Z3Solver.solve(astSMT)
    val smtModel = Z3Solver.getModel(astSMT, translator.getDefinedSymbols.toList)
    val astModel = translator.getASTModel(newAST, smtModel)
    val exactValue = astModel(List())
    
    if (approximateValue == exactValue) {
      Some(exactModel)
    } else {
      None
    }
  }
  
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
        var currentModel = Map() : Model
        for ((c,i) <- children zip children.indices) {
          val newModel = reconstructAST(c, i :: path, appModel, sourceToEncoding, pmap)
          
          // TODO: fix when doing patching
          currentModel = currentModel ++ newModel
        }
        
        currentModel = currentModel + (path -> appModel(sourceToEncoding(path)))
        
        currentModel
      }
      
      
    }
  }
  
  // Given an original formula (ast), and a model over an approximate formula (model).
  // created using a PathMap (sourceToEncoding), translate it to a model over the original formula
  def reconstruct(ast : AST, model : Model, sourceToEncoding : PathMap, pmap : PrecisionMap[T]) : Model = {
    reconstructAST(ast, List(), model, sourceToEncoding, pmap)
  }
}