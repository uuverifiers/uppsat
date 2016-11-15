package uppsat

class ModelReconstuctor[T](approximation : Approximation[T]) {
  type Model = Map[Node, Node]
  
  var constructedModel = None : Option[Model]
  var updatedPrecisionMap = None : Option[PrecisionMap[T]]
  // TODO: should we do this?
  var failed = false
  
  def validateNode(node : InternalNode, model : Model, currentModel : Model, nodeMap : Map[Node, Node]) : Option[Model] = {
    // Which approximate node does the original node correspond to?
    // nodeMap has the answer
    val approximateValue = model(nodeMap(node))
    val realDesc = node.desc.map(x => currentModel(nodeMap(x)))
    val newNode = InternalNode(node.symbol, realDesc)
    val translator = new SMTTranslator(approximation.outputTheory)
    val nodeSMT = translator.translateNoAssert(newNode)
    
    val result = Z3Solver.solve(nodeSMT)
    val smtModel = Z3Solver.getModel(nodeSMT, translator.getDefinedSymbols.toList)
    val exactModel = translator.getNodeModel(smtModel)
    val exactValue = exactModel(newNode)
    
    if (approximateValue == exactValue) {
      Some(currentModel)
    } else {
      None
    }
  }
  
  // TODO: Do we want the type partialModel / partialPrecisionMap
  def reconstructNode(node : Node, model : Model, nodeMap : Map[Node, Node], pmap : PrecisionMap[T]) : (Model, PrecisionMap[T]) = {
    node match {
      case intNode @ InternalNode(symbol, desc) => {
        var currentModel = model
        var currentPmap = PrecisionMap[T]()
        for (d <- desc) {
          val (newModel, newPmap) = reconstructNode(d, model, nodeMap, pmap)
          
          // TODO: fix when doing patching
          currentModel = currentModel ++ newModel
          currentPmap = currentPmap.merge(newPmap)
        }
        
        validateNode(intNode, model, currentModel, nodeMap) match {
          case None => {
            failed = true
            currentPmap = currentPmap.update(node, approximation.refine(pmap(node)))
          }
          case Some(newModel) => // update Model
        }
        
        (currentModel, currentPmap)
      }
      
      case leafNode @ LeafNode(symbol) => {
        if (symbol.theory.isDefinedLiteral(symbol)) {
          (Map(leafNode -> leafNode), PrecisionMap[T]())
        } else {
          (Map(leafNode -> model(leafNode)), PrecisionMap[T]())
        }
      }
    }
  }
  
  def reconstruct(node : Node, model : Model, nodeMap : Map[Node, Node], pmap : PrecisionMap[T]) : Boolean = {
      failed = false
      val (currentModel, currentPmap) = reconstructNode(node, model, nodeMap, pmap)
      if (failed) {
        updatedPrecisionMap = Some(pmap.merge(currentPmap))
        false
      } else {
        constructedModel = Some(currentModel)
        true
      }  
  }
}