package uppsat;


import uppsat.precision.PrecisionMap
import uppsat.Timer.TimeoutException
import uppsat.theory.BooleanTheory._
import uppsat.theory.RealTheory._
import uppsat.theory._
import uppsat.ast._
import uppsat.parser._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.IntegerTheory._
import uppsat.solver._
import uppsat.approximation.components._
import uppsat.precision.PrecisionMap.Path
//import uppsat.Encoder.PathMap
import uppsat.ModelEvaluator.Model
import uppsat.globalOptions._

import uppsat.ApproximationSolver.Answer
import uppsat.ApproximationSolver.Unknown
import uppsat.ApproximationSolver.Unsat
import uppsat.ApproximationSolver.Sat
import uppsat.ApproximationSolver.Answer
import uppsat.approximation.fpa.smallfloats._
import uppsat.approximation.fpa.reals._
import uppsat.approximation.fpa.fixpoint._
import uppsat.approximation.components._
import ap.parser.smtlib
import uppsat.approximation.Approximation

object globalOptions {
  // FLAGS
  var REACHED_MAX_PRECISON = false
  
  val VERSION = "0.5"

  var RANDOM_SEED = 0
  var VERBOSE = false
  var STATS = false
  var MODEL = false
  var FORMULAS = false
  var DEBUG = false
  var DEADLINE : Option[Long] = None
  var STARTTIME : Option[Long] = None
  var PARANOID = false
  var SURRENDER = false

   val REG_SOLVERS = Map( "z3" -> new Z3Solver(), 
                         "mathsat" -> new MathSatSolver("Mathsat", ""),                         
                         "acdcl" -> new MathSatSolver("ACDCL (Mathsat)", "-theory.fp.mode=2 "), 
                         "nlsat" -> new Z3Solver("NLSAT","(check-sat-using qfnra-nlsat)\n")) 
                         
  val REG_APPROXS = Map( "ijcar" ->  new Approximation(IJCARSmallFloatsApp), 
                          "saturation" ->  new Approximation(FxPntSmallFloatsApp), 
                          "reals" ->  new Approximation(FPARealApp),
                          "reals-node-by-node" ->  new Approximation(FPARealNodeByNodeApp),
                          "saturation_reals" -> new Approximation(FxPntFPARealApp),
                          "fixedpoint" ->  new Approximation(FPABVApp),
                          "fixedpoint-node-by-node" ->  new Approximation(FPABVNodeByNodeApp),                          
                          "fixedpoint-no-reconstruct" ->  new Approximation(FPABVEmptyApp),
                          "ijcar-node-by-node" -> new Approximation(IJCARSmallFloatsNodeByNodeApp),
                          "ijcar-no-reconstruct" -> new Approximation(IJCARSmallFloatsEmptyapp)
                          
                         ) //"empty" -> EmptyApproximation) 
                         
  var approximation = "ijcar"
  var backend = "z3"
  var validator = "z3"

  def getApproximation = REG_APPROXS(approximation.toLowerCase())

  def getBackendSolver = REG_SOLVERS(backend.toLowerCase())

  def getValidator = REG_SOLVERS(validator.toLowerCase())

  def verbose(str : String) = {
    if (globalOptions.VERBOSE) {
      println(str)
    }
  }

  def debug(str : String) = {
    if (globalOptions.DEBUG) {
      println(str)
    }
  }

  def remainingTime : Option[Long] = {
    DEADLINE match {
      case None => None
      case Some(t) => Some(DEADLINE.get - (System.currentTimeMillis() - STARTTIME.get))
    }
  }

  def checkTimeout(msg : String = "") = {
    DEADLINE match {
      case None => ()
      case Some(t) => if (System.currentTimeMillis() - STARTTIME.get >= t) throw new TimeoutException(msg)
    }
  }
}


object main {
  
  def printUsage() = {
    println("UppSAT version " + globalOptions.VERSION)
    println("Usage: uppsat [-options] input file")
    println("Options:")
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
    println("\t -t=NUM - set a soft timeout in seconds. Soft means that timeout is checked between iterations only.")
    
    
  }
  
  def printHelpInfo() = {
    println("Input file missing. Call uppsat -h or uppsat -help for usage help.")
  }
  
  /**
   * Parses argument and sets globalOptions accordingly.
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
        case "-h" | "-help" => printUsage()
        case "-f" => globalOptions.FORMULAS = true
        case "-surrender" => globalOptions.SURRENDER = true
        
        case backend(solver) => 
            if (globalOptions.REG_SOLVERS.contains(solver))
              globalOptions.backend = solver
            else
              throw new Exception("Unsupported solver")
            
        case validator(solver) => 
            if (globalOptions.REG_SOLVERS.contains(solver))
              globalOptions.validator = solver
            else
              throw new Exception("Unsupported solver")
        
        case appPattern(app) =>
          if (globalOptions.REG_APPROXS.contains(app))
              globalOptions.approximation = app
            else
              throw new Exception("Unsupported approximation")
        
        case timeoutPattern(t) => {
          globalOptions.DEADLINE = Some(t.toInt * 1000)
        }
        
        case seedPattern(s) => {
          globalOptions.RANDOM_SEED = s.toInt
        }
               
        case dashPattern() => printUsage()
        case _ => true
      }
      false
  }
  
  def main_aux(args : Array[String]) : Answer = {
    import java.io._
    import scala.collection.JavaConversions._
    
    
    globalOptions.STARTTIME = Some(System.currentTimeMillis())
    
    for (a <- args) yield {
      if (parseArgument(a)) {
        println("Unrecognized argument: " + a)
        printUsage()
        return Unknown
      }
        
    }
      
    val files = args.filterNot(_.startsWith("-")).toList  
    
    if (files.isEmpty) {
       printHelpInfo()
       Unknown
    } else {
      val reader = () => new java.io.BufferedReader (new java.io.FileReader(new java.io.File(files.head)))            
      val l = new smtlib.Yylex(reader())
      val p = new smtlib.parser(l)
      val script = p.pScriptC
      Timer.reset
      Timer.measure("main") {
        Interpreter.reset()
        Interpreter.interpret(script)
      }

      if (globalOptions.MODEL)
        Interpreter.myEnv.result match {
          case Sat(model) => {
            println("<MODEL>")
            for ((k, v) <- model)
              println(k + "," + v)
            println("</MODEL>")
          }
          case _ => 
        }
      if (globalOptions.STATS) {
        println(Timer.stats)
        println(":max_precision " + globalOptions.REACHED_MAX_PRECISON)
      }
      Interpreter.myEnv.result
    }
  }
  
  def main(args: Array[String]) = {
    
    verbose("Args: " + args.mkString("|"))
    try {
      main_aux(args) match {
        case Sat(_) => System.exit(10)
        case Unsat   => System.exit(20)
        case Unknown => System.exit(30)        
      }
    } catch {
      case to : TimeoutException => {
        println("timeout")
      }
      case e : Exception => {
        println("Unhandled error: " + e)
        println(e.getStackTraceString)
        println("terminating")
      }
    }
  }   
}

