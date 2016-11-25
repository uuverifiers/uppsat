package uppsat

import uppsat.PrecisionMap.Path

class ModelReconstuctor[T](approximation : Approximation[T]) {
  type Model = Map[AST, AST]
  
  var constructedModel = None : Option[Model]
  var updatedPrecisionMap = None : Option[PrecisionMap[T]]
  // TODO: should we do this?
  var failed = false
  
  def validateAST(ast : AST, model : Model, currentModel : Model, sourceToEncoding : Map[AST, AST]) : Option[Model] = {
    // Which approximate ast does the original ast correspond to?
    // sourceToEncoding has the answer
    val approximateValue = model(sourceToEncoding(ast))
    val realDesc = ast.children.map(x => currentModel(sourceToEncoding(x)))
    val newAST = AST(ast.symbol, realDesc)
    val translator = new SMTTranslator(approximation.outputTheory)
    val astSMT = translator.translateNoAssert(newAST)
    
    val result = Z3Solver.solve(astSMT)
    val smtModel = Z3Solver.getModel(astSMT, translator.getDefinedSymbols.toList)
    val exactModel = translator.getASTModel(smtModel)
    val exactValue = exactModel(newAST)
    
    if (approximateValue == exactValue) {
      Some(currentModel)
    } else {
      None
    }
  }
  
  // TODO: Do we want the type partialModel / partialPrecisionMap
  def reconstructAST(ast : AST, prefix : Path, model : Model, sourceToEncoding : Map[AST, AST], pmap : PrecisionMap[T]) : (Model, PrecisionMap[T]) = {
    ast match {
      case leafAST @ AST(symbol, List()) => {
        if (symbol.theory.isDefinedLiteral(symbol)) {
          (Map(leafAST -> leafAST), PrecisionMap[T]())
        } else {
          (Map(leafAST -> model(leafAST)), PrecisionMap[T]())
        }
      }
      
      case intAST @ AST(symbol, children) => {
        var currentModel = model
        var currentPmap = PrecisionMap[T]()
        for ((c,i) <- children zip children.indices) {
          val (newModel, newPmap) = reconstructAST(c, i :: prefix, model, sourceToEncoding, pmap)
          
          // TODO: fix when doing patching
          currentModel = currentModel ++ newModel
          currentPmap = currentPmap.merge(newPmap)
        }
        
        validateAST(intAST, model, currentModel, sourceToEncoding) match {
          case None => {
            failed = true
            currentPmap = approximation.unsatRefine(ast, List(), pmap)
          }
          case Some(newModel) => // update Model
        }
        
        (currentModel, currentPmap)
      }
      
      
    }
  }
  
  def reconstruct(ast : AST, model : Model, sourceToEncoding : Map[AST, AST], pmap : PrecisionMap[T]) : Boolean = {
      failed = false
      val (currentModel, currentPmap) = reconstructAST(ast, List(), model, sourceToEncoding, pmap)
      if (failed) {
        updatedPrecisionMap = Some(pmap.merge(currentPmap))
        false
      } else {
        constructedModel = Some(currentModel)
        true
      }  
  }
}