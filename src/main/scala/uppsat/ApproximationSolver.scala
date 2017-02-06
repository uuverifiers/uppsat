package uppsat

import uppsat.precision.PrecisionMap
import uppsat.theory.BooleanTheory._
import uppsat.theory._
import uppsat.ast._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.IntegerTheory._
import uppsat.solver._
import uppsat.approximation._
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.globalOptions._


object ApproximationSolver {
  
  type ExtModel = Map[ConcreteFunctionSymbol, String]
  
  trait Answer
  
  case class Sat(model : ExtModel) extends Answer
  case object Unsat extends Answer
  case object Unknown extends Answer
  
  
  def solve(formula : AST, translator : SMTTranslator, approximation : Approximation) : Answer = {
    verbose("-----------------------------------------------")
    verbose("Starting Approximation Framework")
    verbose("-----------------------------------------------")   
    verbose(translator.translate(formula))
    val startTime = System.currentTimeMillis
    val retVal = loop(formula : AST, translator : SMTTranslator, approximation : Approximation) 
    val stopTime = System.currentTimeMillis
    
    
    verbose("Solving time: " + (stopTime - startTime) + "ms") 
    
    //ModelReconstructor.stopOnlineSolver()
    
    retVal match {
      case Sat(model) => {
        verbose("Model found:\n" + model.mkString("\t", "\n\t", "\n"))        
        println("sat")
        Sat(model)
      }
      case Unsat => {        
        println("unsat")
        Unsat
      }
      case Unknown => {        
        println("unknown")
        Unknown
      }
    }
  }
  
  
  
  def loop(formula : AST, translator : SMTTranslator, approximation : Approximation) : Answer = {  
    var pmap = PrecisionMap[approximation.P](formula)(approximation.precisionOrdering)
    pmap = pmap.cascadingUpdate(formula, approximation.precisionOrdering.minimalPrecision)
    var iterations = 0
    
    def tryReconstruct(encodedSMT : String) : (Option[ExtModel], Option[PrecisionMap[approximation.P]]) = Timer.measure("tryReconstruct") {
      val stringModel = Z3Solver.getModel(encodedSMT, translator.getDefinedSymbols.toList)
      val appModel = translator.getModel(formula, stringModel)
      
      debug("Approximate model: " + appModel.getAssignmentsFor(formula).mkString("\n\t") + "\n")
      verbose("Decoding model ... ")
      
      val decodedModel = approximation.decodeModel(formula, appModel, pmap)
      val appAssignments = decodedModel.getAssignmentsFor(formula)
      
      debug("Decoded model: \n" + appAssignments.mkString("\n\t") + "\n")
      verbose("Reconstructing model ...")
      
      val reconstructedModel = approximation.reconstruct(formula, decodedModel)
      val assignments = reconstructedModel.getAssignmentsFor(formula)
      
      debug("Reconstructed model: \n" + appAssignments.mkString("\n\t") + "\n")
      verbose("Validating model ...")
      
      verbose("Model comparison : ")
      if (globalOptions.VERBOSE)
        formula.ppWithModels("", appModel, reconstructedModel)
      
      if (ModelReconstructor.valAST(formula, assignments.toList, approximation.inputTheory, Z3Solver)) {
        val extModel =
          for ((symbol, value) <- reconstructedModel.getModel) yield {
          (symbol, value.symbol.theory.toSMTLib(value.symbol) )
        }
        (Some(extModel), None)
      } else {
        if (pmap.isMaximal) {
          verbose("Model reconstruction failed: maximal precision reached")
          return (None, None)
        } else {
          verbose("Model reconstruction failed: refining precision")            
          val newPmap = approximation.satRefine(formula, decodedModel, reconstructedModel, pmap)
          newPmap.characterize
          (None, Some(newPmap))
        }
      }      
    }    
       
   
    while (checkTimeout) {
      iterations += 1
      verbose("-----------------------------------------------")
      verbose("Starting iteration " + iterations)
      verbose("-----------------------------------------------")
      
      val encodedFormula = approximation.encodeFormula(formula, pmap) 
      //encodedFormula.prettyPrint
      val encodedSMT = translator.translate(encodedFormula)

      verbose(encodedSMT)
      
      if (Z3Solver.solve(encodedSMT)) {
        val (extModel, newPMap) = tryReconstruct(encodedSMT)
        (extModel, newPMap) match {
          case (Some(model), _) => return Sat(model)
          case (_, Some(p)) => pmap = pmap.merge(p)
          case (_, None) => throw new Exception("Loop ???")
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
    }
    
    return Unknown
    //throw new Exception("Main loop exited without return-value.")
  }    
}