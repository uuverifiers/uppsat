package uppsat

import uppsat.precision.PrecisionMap
import uppsat.theory.BooleanTheory._
import uppsat.theory._
import uppsat.ast._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.RealTheory._
import uppsat.solver._
import uppsat.approximation.components._
import uppsat.precision.PrecisionMap.Path
import uppsat.ModelEvaluator.Model
import uppsat.globalOptions._
import uppsat.approximation.Approximation

/** Static object which is the main control structure for the approximation framework.
  *
  *
  */
object ApproximationSolver {

  type ExtModel = Map[ConcreteFunctionSymbol, String]

  trait Answer
  case class Sat(model : ExtModel) extends Answer
  case object Unsat extends Answer
  case object Unknown extends Answer
  /** Solves formula by means of approximation.
 	  *
	  * @param formula The formula to be solved.
	  * @param translator SMT-translator translating formulas to SMT and back.
	  *
	  * @return Sat, Unsat or Unknown depending on the formula.
 	  */
  def solve(formula : AST, translator : SMTTranslator, approximation : Approximation) : Answer = {
    verbose("-----------------------------------------------")
    verbose("Starting Approximation Framework")
    verbose("-----------------------------------------------")
    checkTimeout("solve")
    if (globalOptions.FORMULAS)
      println(translator.translate(formula))
    
    val startTime = System.currentTimeMillis
    val retVal = loop(formula : AST, translator : SMTTranslator, approximation : Approximation) 
    val stopTime = System.currentTimeMillis
    
     
    verbose("Solving time: " + (stopTime - startTime) + "ms") 
    
    // TODO: (Aleks) Do we need to stop the online solver or not?
    //ModelReconstructor.stopOnlineSolver()
    
    retVal match {
      case Sat(model) => println("sat")
      case Unsat => println("unsat")
      case Unknown => println("unknown")
    }
    retVal
  }
  
  
  
  def loop(formula : AST, translator : SMTTranslator, approximation : Approximation) : Answer = {  
    var pmap = PrecisionMap[approximation.P](formula)(approximation.precisionOrdering)
    pmap = pmap.cascadingUpdate(formula, approximation.precisionOrdering.minimalPrecision)
    var iterations = 0     
    
    val smtSolver = globalOptions.getBackendSolver
    
    def tryReconstruct(encodedFormula : AST, stringModel : Map[String, String]) : (Option[ExtModel], Option[PrecisionMap[approximation.P]]) = Timer.measure("tryReconstruct") {
      // MAJORTODO : getstringmodel called?
      val appModel = translator.getModel(encodedFormula, stringModel)
      
      println("appModel")
      println(appModel)
      
      verbose("Decoding model ... ")
      val decodedModel = approximation.decodeModel(formula, appModel, pmap)

      verbose("Reconstructing model ...")

      val reconstructedModel = approximation.reconstruct(formula, decodedModel)

      val assignments = reconstructedModel.toMap

      verbose("Validating model ...")

      if (ModelEvaluator.valAST(formula, assignments.toList, approximation.inputTheory, smtSolver)) {
        val extModel =
          for ((symbol, value) <- reconstructedModel.toMap) yield {
          (symbol, value.symbol.theory.symbolToSMTLib(value.symbol) )
        }
        (Some(extModel), None)
      } else {
        if (pmap.isMaximal) {
          verbose("Model reconstruction failed: maximal precision reached")
          return (None, None)
        } else {
          verbose("Model reconstruction failed: refining precision")       
          if (globalOptions.VERBOSE) {
            println("Comparing decoded Model with reconstructed Model:")
            formula.ppWithModels("->", decodedModel, reconstructedModel)
          }
          val newPmap = approximation.satRefine(formula, decodedModel, reconstructedModel, pmap)
          newPmap.characterize
          (None, Some(newPmap))
        }
      }      
    }    
       
   
    while (true) {
      Timer.newIteration
      iterations += 1
      verbose("-----------------------------------------------")
      val tString = 
        if (globalOptions.DEADLINE.isDefined)
          " (" + ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt + " seconds left)"
        else
          ""
      verbose("Starting iteration " + iterations + tString)
      verbose("-----------------------------------------------")
      checkTimeout("iteration " + iterations)
      val encodedFormula = if (!pmap.isMaximal) 
                              approximation.encodeFormula(formula, pmap)
                           else
                              formula
                              
      val encodedSMT = translator.translate(encodedFormula)

      if (globalOptions.FORMULAS)
        println(encodedSMT)
      
      val maybeModel = smtSolver.getStringModel(encodedSMT, translator.getDefinedSymbols.toList)
      if (maybeModel.isDefined) {
        val (extModel, newPMap) = tryReconstruct(encodedFormula, maybeModel.get)
        (extModel, newPMap) match {
          case (Some(model), _) => return Sat(model)
          case (_, Some(p)) => pmap = pmap.merge(p)
          case (None, None) => verbose("Approximate model not found: maximal precision reached.")          
                               return Unsat
          case (_, None) => verbose("Reconstruction yielded unknown results")
                            pmap = approximation.unsatRefine(formula, List(), pmap)
        }          
      } else {
        if (pmap.isMaximal) {
          verbose("Approximate model not found: maximal precision reached.")          
          return Unsat
        } else {
          verbose("Approximate model not found: refining precision.")            
          pmap = approximation.unsatRefine(formula, List(), pmap)
        }
      }
      
      if (pmap.isMaximal) {
        if (globalOptions.SURRENDER) {
          println("Surrendering")
          return Unknown
        }
        
        if (globalOptions.DEADLINE.isDefined)
          println("Full precision search (" + ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt + " seconds left)")
        else
          println("Full precision search")        
          
        globalOptions.REACHED_MAX_PRECISON = true
        
        val validator = globalOptions.getValidator  
        val smtFormula = translator.translate(formula)
        val stringModel = validator.getStringModel(smtFormula, translator.getDefinedSymbols.toList) 
        if (stringModel.isDefined) {
          val model = translator.getModel(formula, stringModel.get) 
          val extModel =
              for ((symbol, value) <- model.toMap) yield {
              (symbol, value.symbol.theory.symbolToSMTLib(value.symbol) )
              }
          return Sat(extModel)
        }          
        else 
          return Unsat
      }
    }
    
    return Unknown
    //throw new Exception("Main loop exited without return-value.")
  }    
}
