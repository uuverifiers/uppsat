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
  
  def floatingpoint() = {
    import uppsat.FloatingPointTheory._
    
    
    val rm = Leaf(RoundToZero)
    val FP_3_3 = FPSortFactory(List(3,3))
    val x = new FPVar("x", FP_3_3)
    val y = new FPVar("y", FP_3_3)
    val FPAdd = FPAdditionFactory(List(FP_3_3))
    val xNode = Leaf(x)
    val yNode = Leaf(y)
    val addNode = AST(FPAdd, List(rm, xNode, yNode))
    val FPEq = FPEqualityFactory(List(FP_3_3))    
    val rootNode = AST(FPEq, List(addNode, xNode))
    
    (rootNode, List(x, y))
  }
  
  def main(args: Array[String]) = {
    val (formula, vars) = floatingpoint()
    println("<<<Formula>>>")
    formula.prettyPrint
    
    val enc = new Encoder[Int](IntApproximation)
    val myIntOrdering = new IntPrecisionOrdering(10)
    var pmap = PrecisionMap[Int](myIntOrdering)
    pmap = pmap.cascadingUpdate(List(0), formula, 1)
    val translator = new SMTTranslator(FloatingPointTheory)

    import uppsat.PrecisionMap.Path
    import uppsat.Encoder.PathMap
    import uppsat.ModelReconstructor.Model

    var iterations = 0

    var finalModel = None: Option[Map[ConcreteFunctionSymbol, String]]
    var haveAnAnswer = false
    var encodedFormula = formula
    var encodedSMT = ""
    var maxPrecisionTried = false
    while (!haveAnAnswer && !maxPrecisionTried) {
      var haveApproxModel = false

      // TODO: fix maximal pmap
      while (!haveApproxModel && !maxPrecisionTried) {
        iterations += 1
        println("Starting iteration " + iterations)
        
        if (pmap.isMaximal)
          maxPrecisionTried = true
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
        
        val assignments = for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield {
          val value = decodedModel(label)
          (symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
        }

        if (ModelReconstructor.valAST(formula, assignments.toList, FloatingPointTheory, Z3Solver)) {
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
     } else if (pmap.isMaximal) {
      println("Precision maximal...")
    } else{
      println("Why did we stop trying?")
    }
  }
}
