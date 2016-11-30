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

    ((x === (y - 4)) & ((x + y) === 6), List(x, y))

  }
  
  def main(args: Array[String]) = {
    val (formula, vars) = integer()
    println("<<<Formula>>>")
    formula.prettyPrint
    
    val enc = new Encoder[Int](IntApproximation)
    var pmap = PrecisionMap[Int]()
    pmap = pmap.cascadingUpdate(List(0), formula, 1)
    val translator = new SMTTranslator(IntegerTheory)

    import uppsat.PrecisionMap.Path
    import uppsat.Encoder.PathMap
    import uppsat.ModelReconstructor.Model

    var iterations = 0

    var finalModel = None: Option[Map[ConcreteFunctionSymbol, String]]
    var haveAnAnswer = false
    var encodedFormula = formula
    var encodedSMT = ""

    while (!haveAnAnswer && iterations < 10) {
      var haveApproxModel = false

      // TODO: fix maximal pmap
      while (!haveApproxModel && iterations < 10) {
        iterations += 1
        println("Starting iteration " + iterations)
        
        encodedFormula = enc.encode(formula, pmap)   
        encodedSMT = translator.translate(encodedFormula)
        val result = Z3Solver.solve(encodedSMT)

        if (result) {
          haveApproxModel = true
        } else {
          println("No approximative model found> updating precisions")
          // TODO: Unsat core reasoning
          pmap = IntApproximation.unsatRefine(formula, List(), pmap)
        }
      }

      if (haveApproxModel) {
        val stringModel = Z3Solver.getModel(encodedSMT, translator.getDefinedSymbols.toList)
        val appModel = translator.getModel(formula, stringModel)
        val reconstructor = new ModelReconstructor[Int](IntApproximation)         
        val reconstructedModel = reconstructor.reconstruct(formula, appModel) 
        val decodedModel = IntApproximation.decodeModel(formula, reconstructedModel, pmap)
        
        val assignments = for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield
          (symbol.toString(), decodedModel(label).symbol.toString())

        if (ModelReconstructor.valAST(formula, assignments.toList, IntApproximation.inputTheory, Z3Solver)) {
          haveAnAnswer = true
          finalModel = Some((for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield {
            (symbol, decodedModel(label).toString())
          }).toMap)
          
        } else {
          println("Model reconstruction failed> updating precisions")
          val newPmap = IntApproximation.satRefine(formula, appModel, decodedModel, pmap)
          pmap = pmap.merge(newPmap)
        }
      }
    }

    if (haveAnAnswer == true) {
      println("Found model")        
      println(finalModel.get)
     } else {
      println("No model found...")
    }
  }
}
