package uppsat;


import ap.parser.smtlib

import uppsat.ApproximationSolver.{Answer, Sat, Unknown, Unsat}
import uppsat.RegisteredApproximations.regApproxs
import uppsat.Timer.TimeoutException
import uppsat.approximation.Approximation
import uppsat.globalOptions._
import uppsat.parser._
import uppsat.solver._

/** Stores (for convenience) options which are used by all parts of UppSAT
  *
  */
object globalOptions {
  // TODO (ptr): Change version when done with refactoring.

  /** Current version of UppSAT */
  val VERSION = "0.5"

  /** Deadline for overall search */
  var DEADLINE : Option[Long] = None

  /** Enables some extra output and saving of auxilliary files */
  var DEBUG = false

  /** Display formulas */
  var FORMULAS = false

  /** Display models */
  var MODEL = false

  /** No solving, only parsing, etc. */
  var NO_RUN = false

  /** Double check many answers */
  var PARANOID = false

  /** Random seed */
  var RANDOM_SEED = 0

  /** Indicating whether max precision has been reached */
  var REACHED_MAX_PRECISON = false

  /** Starttime of solving process */
  var STARTTIME : Option[Long] = None

  /** Display statistics */
  var STATS = false

  /** Do not do full precision search */
  var SURRENDER = false

  /** (Lots of) extra output */
  var VERBOSE = false

  /** Precision options for FixedPoint approximation. */
  var FX_MIN_PRECISION =
    uppsat.approximation.fpa.fixpoint.FPABVContext.defaultMinPrecision
  var FX_MAX_PRECISION =
    uppsat.approximation.fpa.fixpoint.FPABVContext.defaultMaxPrecision
  var FX_PREC_INC =
    uppsat.approximation.fpa.fixpoint.FPABVContext.defaultPrecIncrement

  // Choosen approximation/backend/validator
  var approximation = "ijcar"
  var backend = "z3"
  var validator = "z3"

  // Storing statistics
  // TODO (ptr): Put in separate object?
  var STATS_ITERATIONS = 0


  /** Instantiates the given solver.
    *
    * @param str Name of solver
    */
  def registeredSolvers(str : String) = {
    str match {
      case "z3" => new Z3Solver()
      case "mathsat" => new MathSatSolver("Mathsat", "")
      case "acdcl" => new MathSatSolver("ACDCL (Mathsat)", "-theory.fp.mode=2 ")
      case "nlsat" => new Z3Solver("NLSAT","(check-sat-using qfnra-nlsat)\n")
      case _ => {
        val msg = "Trying to instantiate unregistered solver: " + str
        throw new Exception(msg)
      }
    }
  }


  /** Instantiates the given approximation.
    *
    * @param str Name of approximation
    */
  def instantiateApproximation() : Approximation = {
    val str = approximation.toLowerCase()
    if (regApproxs contains str)
      regApproxs(str)._2()
    else
      throw new Exception(s"Unregistered approximation: $str")
  }

  /** Get the active backend solver.
    */
  def getBackendSolver = registeredSolvers(backend.toLowerCase())

  /** Get the active validator solver.
    */
  def getValidator = registeredSolvers(validator.toLowerCase())

  /** Prints str if verbose mode is active.
    */
  def verbose(str : String) = {
    if (globalOptions.VERBOSE) {
      println(str)
    }
  }

  /** Prints str if debug mode is active.
    */
  def debug(str : String) = {
    if (globalOptions.DEBUG) {
      println(str)
    }
  }

  /** Remaining time before deadline is violated.
    */
  def remainingTime : Option[Long] = {
    DEADLINE match {
      case None => None
      case Some(t) =>
        Some(DEADLINE.get - (System.currentTimeMillis() - STARTTIME.get))
    }
  }

  /** Remaining seconds before deadline is violated
    *
    * @return Number of seconds before deadline, -1 if no deadline
    */
  def remainingSeconds() : Int = {
    DEADLINE match {
      case None => -1
      case Some(t) => {
        val remTime =
          DEADLINE.get - (System.currentTimeMillis() - STARTTIME.get)
        (remTime/1000.0).ceil.toInt
      }
    }
  }

  /** Throw exception if deadline is violated.
    * @throws TimeoutException if deadline is violated
    */
  def checkTimeout(msg : String = "") = {
    DEADLINE match {
      case None => ()
      case Some(t) =>
        if (System.currentTimeMillis() - STARTTIME.get >= t)
          throw new TimeoutException(msg)
    }
  }
}

/** Main object.
  */
object main {

  /** Prints help text in console.
    */
  def printUsage() = {
    println("UppSAT version " + globalOptions.VERSION)
    println("Usage: uppsat [-options] input file")
    println("Options:")
    println("\t-a - print detailed approximation information")
    println("\t-v - verbose output")
    println("\t-s - print statistics")
    println("\t-m - print model (debug purposes)")
    println("\t-d - debugging output")
    println("\t-p - run a second check using z3 to verify internal queries")
    println("\t-backend= - use one of the following backends:")
    println("\t\t z3 (default)")
    println("\t\t mathsat : MathSat")
    println("\t\t acdcl : MathSat(ACDCL)")
    println("\t\t nlsat : Z3 using qfnrq-nlsat tactic")
    println("\t-validator= - use one of the following backends:")
    println("\t\t z3 (default)")
    println("\t\t mathsat : MathSat")
    println("\t\t acdcl : MathSat(ACDCL)")
    println("\t\t nlsat : Z3 using qfnrq-nlsat tactic")
    println("\t -app= - use one of the following approximations:")
    println("\t\t ijcar : Smallfloats (node based reconstruction)")
    println("\t\t saturation : Smallfloats (fixpoint based reconstruction)")
    println("\t\t fixedpoint : BitVector (node based reconstruction)")
    println("\t\t reals : Reals (node based reconstruction)")
    println("\t\t empty : Empty Approximation (for debug purposes)")
    println("\t -t=NUM - set a soft timeout in seconds." +
              "Soft means that timeout is checked between iterations only.")
  }

  /** Print short help in console.
    */
  def printHelpInfo() = {
    println("Input file missing. Call uppsat -h or uppsat -help for help.")
  }

  /**
    * Prints description of approximations.
    */
  def printDescriptions() = {
    val maxLength = regApproxs.map(_._2._1.length).max + 3
    val title = "Approximation:"
    println(title + " "*(maxLength - title.length) + "Description:")
    println("-"*(maxLength + regApproxs.map(_._2._1.length).max))
    for ((app, (desc, _)) <- regApproxs) {
      println(app + " "*(maxLength - app.length) + desc)
    }
  }

  /**
    * Parses argument and sets globalOptions accordingly.
    *
    * Results of parsing is stored in global variables.
    *
    * @param arg Argument to be parsed
    * @return Returns true if arg was unparseable
    */
  def parseArgument( arg : String) : Boolean = {
    val timeoutPattern = "-t=([0-9.]+)".r
    val seedPattern = "-seed=([0-9.]+)".r
    val appPattern = "-app=(\\S+)".r
    val backend = "-backend=(\\S+)".r
    val validator = "-validator=(\\S+)".r
    val fxPrec = "-fxp=([0-9]+)\\.([0-9]+)-([0-9]+)\\.([0-9]+)".r
    val fxInc = "-fxi=([0-9]+)\\.([0-9]+)".r
    val asd = "-fxp(.*)".r
    val dashPattern = "-.*".r
    arg match {
      case "-test" => {
        globalOptions.STATS = true
        globalOptions.MODEL = true
        globalOptions.VERBOSE = true
        globalOptions.DEBUG = true
        globalOptions.FORMULAS = true
      }
      case "-s" => globalOptions.STATS = true
      case "-m" => globalOptions.MODEL = true
      case "-v" => globalOptions.VERBOSE = true
      case "-d" => globalOptions.DEBUG = true
      case "-p" => globalOptions.PARANOID =  true
      case "-h" | "-help" => {
        printUsage()
        globalOptions.NO_RUN = true
      }
      case "-a" => {
        printDescriptions()
        globalOptions.NO_RUN = true
      }
      case "-f" => globalOptions.FORMULAS = true
      case "-surrender" => globalOptions.SURRENDER = true

      case backend(solver) => globalOptions.backend = solver

      case validator(solver) => globalOptions.validator = solver

      case appPattern(app) => globalOptions.approximation = app

      case timeoutPattern(t) => {
          globalOptions.DEADLINE = Some(t.toInt * 1000)
        }

      case seedPattern(s) => {
        globalOptions.RANDOM_SEED = s.toInt
      }

      case fxPrec(minI, minF, maxI, maxF) => {
        globalOptions.FX_MIN_PRECISION = (minI.toInt, minF.toInt)
        globalOptions.FX_MAX_PRECISION = (maxI.toInt, maxF.toInt)
      }

      case fxInc(incI, incF) => {
        globalOptions.FX_PREC_INC = (incI.toInt, incF.toInt)
      }

      case dashPattern() => printUsage()

      case _ => {
        true
      }
    }
    false
  }

  /** Execute command in args.
    */
  def main_aux(args : Array[String]) : Answer = {
    import java.io._

    globalOptions.STARTTIME = Some(System.currentTimeMillis())

    for (a <- args) yield {
      if (parseArgument(a)) {
        println("Unrecognized argument: " + a)
        printUsage()
        return Unknown
      }
    }

    val files = args.filterNot(_.startsWith("-")).toList

    if (globalOptions.NO_RUN) {
      // Do nothing
      Unknown
    } else if (files.isEmpty) {
      printHelpInfo()
      Unknown
    } else {
      val reader =
        () => new java.io.BufferedReader (new java.io.FileReader(
                                            new java.io.File(files.head)))
      val l = new smtlib.Yylex(reader())
      val p = new smtlib.parser(l)
      val script = p.pScriptC
      Timer.reset

      // Measure time to interpret (and execute) whole script
      Timer.measure("main") {
        Interpreter.reset()
        Interpreter.interpret(script)
      }

      // Should we print model?
      if (globalOptions.MODEL)
        Interpreter.myEnv.result match {
          case Sat(model) => {
            println("<MODEL>")
            for ((k, v) <- model)
              println(s"$k, $v")
            println("</MODEL>")
          }
          case _ => ()
        }

      if (globalOptions.STATS) {
        println(Timer.stats)
        println(":max_precision " + globalOptions.REACHED_MAX_PRECISON)
      }

      Interpreter.myEnv.result
    }
  }

  /** Main function.
    */
  def main(args: Array[String]) = {
    verbose("Args: " + args.mkString("|"))

    try {
      main_aux(args) match {
        case Sat(_) => {
          println("sat")
        }

        case Unsat   => {
          println("unsat")
        }

        case Unknown => {
          println("unknown")
        }
      }
    } catch {
      case to : TimeoutException => {
        println("timeout")
      }
      case e : Exception => {
        println("Unhandled error: " + e)
        e.printStackTrace()
      }
    }
  }
}

