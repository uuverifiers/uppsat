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


object ApproximationSolver {
  
  type ExtModel = Map[ConcreteFunctionSymbol, String]
  
  def solve(formula : AST, translator : SMTTranslator, approximation : Approximation) = {
    println(translator.translate(formula))
    val startTime = System.currentTimeMillis
    val retVal = loop(formula : AST, translator : SMTTranslator, approximation : Approximation) 
    val stopTime = System.currentTimeMillis
    
    println("Solving time: " + (stopTime - startTime) + "ms") 
    
    retVal match {
      case Some(model) => {
        println("Model found!")
        println(model.mkString("\t", "\n\t", "\n"))
        Some(model)
      }
      case None => {
        println("No model found!")
        None
      }
    }
  }
  
  def loop(formula : AST, translator : SMTTranslator, approximation : Approximation) : Option[ExtModel] = {  
    
    var pmap = PrecisionMap[approximation.P](approximation.precisionOrdering)
    pmap = pmap.cascadingUpdate(List(0), formula, approximation.precisionOrdering.min)    
    var iterations = 0
    
    def tryReconstruct(encodedSMT : String) : (Option[ExtModel], Option[PrecisionMap[approximation.P]]) = {
      val stringModel = Z3Solver.getModel(encodedSMT, translator.getDefinedSymbols.toList)
      val appModel = translator.getModel(formula, stringModel)
      val decodedModel = approximation.decodeModel(formula, appModel, pmap)
      val reconstructedModel = approximation.reconstruct(formula, decodedModel)
      
      val assignments = for ((symbol, label) <- formula.iterator if (!symbol.theory.isDefinedLiteral(symbol))) yield {
        val value = reconstructedModel(label)
        (symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
      }

      if (ModelReconstructor.valAST(formula, assignments.toList, approximation.inputTheory, Z3Solver)) {
        val extModel =
          (for ((symbol, label) <- formula.iterator 
              if (!symbol.theory.isDefinedLiteral(symbol))) yield {
                (symbol, reconstructedModel(label).toString())
          }).toMap
        (Some(extModel), None)
      } else {
        if (pmap.isMaximal) {
          println("Model reconstruction failed: maximal precision reached")
          return (None, None)
        } else {
          println("Model reconstruction failed: refining precision")            
          val newPmap = approximation.satRefine(formula, appModel, decodedModel, pmap)
          (None, Some(newPmap))
        }
      }      
    }    
       
    // TODO: can we change this into if not maximal pmap    
    while (true) {     

      iterations += 1
      println("-----------------------------------------------")
      println("Starting iteration " + iterations)
      println("-----------------------------------------------")
      
      val encodedFormula = approximation.encodeFormula(formula, pmap) 
      encodedFormula.prettyPrint
      val encodedSMT = translator.translate(encodedFormula)

      println(encodedSMT)
      
      if (Z3Solver.solve(encodedSMT)) {
        val (extModel, newPMap) = tryReconstruct(encodedSMT)
        (extModel, newPMap) match {
          case (Some(model), _) => return extModel
          case (_, Some(p)) => pmap = pmap.merge(p)
          case (_, None) => return None
        }          
      } else {
        if (pmap.isMaximal) {
          println("Approximative model not found: maximal precision reached.")
          return None
        } else {
          println("Approximative model not found: refining precision.")            
        // TODO: Unsat core reasoning            
          pmap = approximation.unsatRefine(formula, List(), pmap)
        }
      }
    }
    throw new Exception("Main loop exited without return-value.")
  }    
}