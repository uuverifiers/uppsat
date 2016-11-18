package uppsat;

object main {
  def boolean() = {    
    import uppsat.BooleanTheory._
    
    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue
   
    val f = a & (!b & (t & (!c)))
    val translator = new SMTTranslator(BooleanTheory)
    val SMT = translator.translate(f)
    println(SMT)
  }
  
  
  def integer() = {
    import uppsat.IntegerTheory._
    import uppsat.BooleanTheory._
    
    val x = new IntVar("x")
    val y = new IntVar("y")
    
    ((x === ( y - 4)) & ( (x + y) === 6), List(x, y))
    
  }
  
  
  def main(args : Array[String]) = {
    val (formula, vars) = integer()
    //val extractSymbols = defSyms.map(_.toString).toList
    println(formula)
    println("<<<SMT Formula>>>")
    val enc = new Encoder[Int]
    var pmap = PrecisionMap[Int]()
    
    pmap = pmap.cascadingUpdate(List(), formula, 1)    
    val translator = new SMTTranslator(IntegerTheory)
    // TODO: How do we solve this logistically
    var sourceToEncoding = Map() : Map[AST, AST]
    
    def tryZ3() = {
      var iterations = 0
      
      var finalModel = None : Option[Map[AST, AST]]
      var haveAnAnswer = false
      var pSMT = ""
      while (!haveAnAnswer && iterations < 100) {
        var haveApproxModel = false
      
        // TODO: fix maximal pmap
        while (!haveApproxModel && iterations < 100) {
          iterations += 1
          println("Starting iteration " + iterations)
          val (pFormula, newASTMap) = enc.encode(formula, pmap)          
          sourceToEncoding = newASTMap
          pSMT = translator.translate(pFormula)
          println(pSMT)
          val result = Z3Solver.solve(pSMT)
          if (result) {
            haveApproxModel= true
          } else {
            println("Increasing all precisions")
            // TODO: Unsat core reasoning
            pmap = pmap.cascadingIncrease(List(), formula)
          }
        }
  
        if (haveApproxModel) {   
          val model = Z3Solver.getModel(pSMT, translator.getDefinedSymbols.toList)
          val nodeModel = translator.getASTModel(model)
          
          val reconstructor = new ModelReconstuctor[Int](IntApproximation)
          val recVal = reconstructor.reconstruct(formula, nodeModel, sourceToEncoding, pmap)
          if (recVal) {
            haveAnAnswer = true
            finalModel = reconstructor.constructedModel
          } else {
            println("Failed, updating precisions: " + reconstructor.updatedPrecisionMap.get)
            pmap = pmap.merge(reconstructor.updatedPrecisionMap.get)
          }
        }
      }
      
      if (haveAnAnswer == true) {
        println("Found model")
        for (v <- vars)
          println(v + "\t" + finalModel.get(v) + "\t (" + finalModel.get(v).getClass + ")")
      } else {  
        println("No model found...")
      }
    }  

    tryZ3()
  }
}
