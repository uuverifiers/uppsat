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
    globalOptions.STATS_ITERATIONS = 0
    var pmap =
      PrecisionMap[approximation.P](formula)(approximation.precisionOrdering)
    pmap =
      pmap.cascadingUpdate(formula,
                           approximation.precisionOrdering.minimalPrecision)


    // Tries to reconstruct stringModel for encodedFormula Returns (Model,
    // newPrecisionMap) with either being None, or both of them if search has
    // completely ended.

    // TODO (ptr): Instead of checking pmap is maximal, this should be
    // refactored
    def tryReconstruct(encodedFormula : AST,
                       stringModel : Map[String, String])
        : (Option[ExtModel], Option[PrecisionMap[approximation.P]]) =
      Timer.measure("tryReconstruct") {
        // MAJORTODO : getstringmodel called?

        verbose("stringModel:")
        verbose("\t" + stringModel.mkString("\n\t"))

        val appModel = translator.getModel(encodedFormula, stringModel)
        verbose("appModel:")
        verbose(appModel.toString())

        val finalModel =
          if (pmap.isMaximal) {
            appModel
          } else {
            verbose("Decoding model ... ")
            val decodedModel = approximation.decodeModel(formula, appModel, pmap)

            verbose("Reconstructing model ...")
            approximation.reconstruct(formula, decodedModel)
          }

        val assignments = finalModel.toMap.toList


        verbose("Validating model ...")
        val isModel =
          ModelEvaluator.validateModel(formula,
                                       assignments,
                                       approximation.inputTheory,
                                       solver)
        if (isModel) {
          val extModel =
            for ((symbol, value) <- finalModel.toMap) yield {
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
              val decodedModel = approximation.decodeModel(formula, appModel, pmap)
              formula.ppWithModels("->", decodedModel, finalModel)
            }


            // TODO (ptr): Refactor, here decodedModel is computed twice.
            val decodedModel = approximation.decodeModel(formula, appModel, pmap)
            val newPmap =
              approximation.satRefine(formula,
                                      decodedModel,
                                      finalModel,
                                      pmap)
            newPmap.characterize
            (None, Some(newPmap))
          }
        }
      }

    // Main solving loop
    while (true) {
      Timer.newIteration
      globalOptions.STATS_ITERATIONS += 1
      verbose("-----------------------------------------------")
      verbose("Starting iteration " + globalOptions.STATS_ITERATIONS)
      if (globalOptions.DEADLINE.isDefined)
          verbose(s"\t${globalOptions.remainingSeconds()} seconds left")
      verbose("-----------------------------------------------")
      checkTimeout("iteration " + globalOptions.STATS_ITERATIONS)
      val encodedFormula = if (!pmap.isMaximal)
                              approximation.encodeFormula(formula, pmap)
                           else
                             formula

      val encodedSMT = translator.translate(encodedFormula)

      if (globalOptions.FORMULAS)
        println(encodedSMT)

      // TODO (ptr): Perhaps only do string-model after we have done just
      // check-sat? Maybe not an issue, but currently up to thousand evals has
      // to be evaluated on UNSAT calls.

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
        globalOptions.REACHED_MAX_PRECISON = true

        verbose("Full precision search")
        if (globalOptions.DEADLINE.isDefined)
          verbose(s"\t${globalOptions.remainingSeconds()} seconds left")

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
