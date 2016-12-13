package uppsat;

import uppsat.precision.PrecisionMap
import uppsat.theory.BooleanTheory._
import uppsat.theory._
import uppsat.ast._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.IntegerTheory._
import uppsat.solver._
import uppsat.approximation._


object main {
  def boolean() = {

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

    val x = new IntVar("x")
    val y = new IntVar("y")

    val rootNode = (x === (y - 4)) & ((x + y) === 6)
    (rootNode, List(x, y), new SMTTranslator(IntegerTheory), IntApproximation)
  }
  
  def floatingpoint() = {
    implicit val rmm = RoundToPositive
    implicit val fpsort = FPSortFactory(List(8,24))
    
    val x = FPVar("x")
    val y = FPVar("y")
    val c : AST = 1.75f
    val rootNode = (x + 1.75f === y) & (x === 2f)
    (rootNode, List(x, y), new SMTTranslator(FloatingPointTheory), SmallFloatsApproximation)
  }
  
  def main(args: Array[String]) = {
    val (formula, vars, translator, approximation) = floatingpoint()
    println("<<<Formula>>>")
    formula.prettyPrint
    
    type P = approximation.precisionOrdering.P
    val enc = new Encoder[P](approximation)    
    var pmap = PrecisionMap[P](approximation.precisionOrdering)
    pmap = pmap.cascadingUpdate(List(0), formula, 0) 

    import uppsat.precision.PrecisionMap.Path
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
        encodedFormula.prettyPrint
        encodedSMT = translator.translate(encodedFormula)
        val result = Z3Solver.solve(encodedSMT)

        if (result) {
          haveApproxModel = true
        } else {
          println("No approximative model found> updating precisions")
          // TODO: Unsat core reasoning
          pmap = approximation.unsatRefine(formula, List(), pmap)
        }
      }

      if (haveApproxModel) {
        val stringModel = Z3Solver.getModel(encodedSMT, translator.getDefinedSymbols.toList)
        val appModel = translator.getModel(formula, stringModel)
        val reconstructor = new ModelReconstructor[P](approximation)         
        val reconstructedModel = reconstructor.reconstruct(formula, appModel) 
        val decodedModel = approximation.decodeModel(formula, reconstructedModel, pmap)
        
        val assignments = for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield {
          val value = decodedModel(label)
          (symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
        }

        if (ModelReconstructor.valAST(formula, assignments.toList, approximation.inputTheory, Z3Solver)) {
          haveAnAnswer = true
          finalModel = Some((for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield {
            (symbol, decodedModel(label).toString())
          }).toMap)
          
        } else {
          println("Model reconstruction failed> updating precisions")
          val newPmap = approximation.satRefine(formula, appModel, decodedModel, pmap)
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
