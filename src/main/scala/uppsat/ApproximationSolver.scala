package uppsat

import uppsat.ModelEvaluator.Model
import uppsat.approximation.Approximation
import uppsat.approximation.components._
import uppsat.ast._
import uppsat.globalOptions._
import uppsat.precision.PrecisionMap
import uppsat.precision.PrecisionMap.Path
import uppsat.solver._
import uppsat.theory._
import uppsat.theory.BooleanTheory._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.RealTheory._

/** Static object which is the main control structure for the approximation
  * framework.
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
  def solve(formula : AST,
            translator : SMTTranslator,
            approximation : Approximation) : Answer = {
    verbose("-----------------------------------------------")
    verbose("Starting Approximation Framework")
    verbose("-----------------------------------------------")
    checkTimeout("solve")
    if (globalOptions.FORMULAS)
      println(translator.translate(formula))

    val startTime = System.currentTimeMillis
    val retVal = loop(formula, translator, approximation)
    val stopTime = System.currentTimeMillis

    verbose("Solving time: " + (stopTime - startTime) + "ms")

    // TODO: Do we need to stop the online solver or not?
    // ModelReconstructor.stopOnlineSolver()

   retVal
  }

  /** Solves formula by means of approximation.
 	  *
	  * @param formula The formula to be solved.
	  * @param translator SMT-translator translating formulas to SMT and back.
	  *
	  * @return Sat, Unsat or Unknown depending on the formula.
 	  */
  // TODO (ptr): Split into smaller functions
  def loop(formula : AST,
           translator : SMTTranslator,
           approximation : Approximation) : Answer = {

    val solver = globalOptions.getBackendSolver
    var iterations = 0
    var pmap =
      PrecisionMap[approximation.P](formula)(approximation.precisionOrdering)
    pmap =
      pmap.cascadingUpdate(formula,
                           approximation.precisionOrdering.minimalPrecision)


    // Tries to reconstruct stringModel for encodedFormula Returns (Model,
    // newPrecisionMap) with either being None, or both of them if search has
    // completely ended.
    def tryReconstruct(encodedFormula : AST,
                       stringModel : Map[String, String])
        : (Option[ExtModel], Option[PrecisionMap[approximation.P]]) =
      Timer.measure("tryReconstruct") {
        // MAJORTODO : getstringmodel called?
        val appModel = translator.getModel(encodedFormula, stringModel)

        verbose("Decoding model ... ")
        val decodedModel = approximation.decodeModel(formula, appModel, pmap)

        verbose("Reconstructing model ...")
        val reconstructedModel =
          approximation.reconstruct(formula, decodedModel)

        val assignments = reconstructedModel.toMap.toList

        verbose("Validating model ...")
        val isModel =
          ModelEvaluator.valAST(formula,
                                assignments,
                                approximation.inputTheory,
                                solver)
        if (isModel) {
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

            val newPmap =
              approximation.satRefine(formula,
                                      decodedModel,
                                      reconstructedModel,
                                      pmap)
            newPmap.characterize
            (None, Some(newPmap))
          }
        }
      }

    // Main solving loop
    while (true) {
      Timer.newIteration
      iterations += 1
      verbose("-----------------------------------------------")
      val tString = 
        if (globalOptions.DEADLINE.isDefined) {
          val remSeconds = ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt
          " (" + remSeconds + " seconds left)"
        } else {
          ""
        }
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

      val maybeModel =
        solver.getStringModel(encodedSMT, translator.getDefinedSymbols.toList)
      if (maybeModel.isDefined) {
        val (extModel, newPMap) = tryReconstruct(encodedFormula, maybeModel.get)
        (extModel, newPMap) match {
          case (Some(model), _) =>
            return Sat(model)
          case (_, Some(p)) =>
            pmap = pmap.merge(p)
          case (None, None) => {
            verbose("Approximate model not found: maximal precision reached.")
            return Unsat
          }
          case (_, None) => {
            verbose("Reconstruction yielded unknown results")
            pmap = approximation.unsatRefine(formula, List(), pmap)
          }
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

        val tString =
          if (globalOptions.DEADLINE.isDefined) {
            val remSeconds =
              ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt
            " (" + remSeconds + " seconds left)"
          } else {
            ""
          }

        println("Full precision search" + tString)

        globalOptions.REACHED_MAX_PRECISON = true

        val validator = globalOptions.getValidator
        val smtFormula = translator.translate(formula)
        val stringModel =
          validator.getStringModel(smtFormula,
                                   translator.getDefinedSymbols.toList)
        if (stringModel.isDefined) {
          val model = translator.getModel(formula, stringModel.get)
          val extModel =
              for ((symbol, value) <- model.toMap) yield {
                (symbol, value.symbol.theory.symbolToSMTLib(value.symbol))
              }
          return Sat(extModel)
        }
        else
          return Unsat
      }
    }

    return Unknown
  }
}
