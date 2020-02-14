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
import uppsat.approximation.smallints.SmallIntsApp
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
  var NO_RUN = false

  def reset() = {
    REACHED_MAX_PRECISON = false
    RANDOM_SEED = 0
    VERBOSE = false
    STATS = false
    MODEL = false
    FORMULAS = false
    DEBUG = false
    DEADLINE = None
    STARTTIME = None
    PARANOID = false
    SURRENDER = false
    NO_RUN = false
  }


  // TODO: It would be nice to specify approximation name, command and object as a tuple

  val solverDescriptions : Map[String, String] = 
    Map("z3" -> "Z3 Solver",
      "mathsat" -> "MathSat solver",
      "acdcl" -> "MathSat solver using ACDCL mode",
      "nlsat" -> "Z3 using NLSAT mode")



  def registeredSolvers(str : String) = {
    str match {
      case "z3" => new Z3Solver() 
      case "mathsat" => new MathSatSolver("Mathsat", "")                         
      case "acdcl" => new MathSatSolver("ACDCL (Mathsat)", "-theory.fp.mode=2 ") 
      case "nlsat" => new Z3Solver("NLSAT","(check-sat-using qfnra-nlsat)\n")  
    }
  }



  // TODO: These descriptions could be more clear
  val approximationDescriptions : Map[String, String] = 
    Map("ijcar" -> "The SmallFloats approximation introduced at IJCAR 2014",
    "ijcar-node-by-node" -> "The SmallFloats approximation introduced at IJCAR 2014 using node-by-node",
    "ijcar-no-reconstruct" -> "The SmallFloats approximation introduced at IJCAR 2014 with no reconstruction",
    "saturation" -> "Saturation based approximation",
    "smallints" -> "SmallInts approximation",
    "reals" -> "Real approximation of floating points",
    "reals-node-by-node" -> "Real approximation evaluating by node-by-node", 
    "saturation_reals" -> "Real approximation using saturation",
    "fixedpoint" -> "Fixed-point approximation of floating points",
    "fixedpoint-node-by-node" -> "Fixed-point approximation of floating points using node-by-node",
    "fixedpoint-no-reconstruct" -> "Fixed-point approximation of floating points with no reconstruction")

  def registeredApproximations(str : String) : Approximation = {
    str match {
      case "ijcar" =>  new Approximation(IJCARSmallFloatsApp)
      case "saturation" =>  new Approximation(FxPntSmallFloatsApp)
      case "smallints" =>  new Approximation(SmallIntsApp)
      case "reals" =>  new Approximation(FPARealApp)
      case "reals-node-by-node" =>  new Approximation(FPARealNodeByNodeApp)
      case "saturation_reals" => new Approximation(FxPntFPARealApp)
      case "fixedpoint" =>  new Approximation(FPABVApp)
      case "fixedpoint-node-by-node" =>  new Approximation(FPABVNodeByNodeApp)                          
      case "fixedpoint-no-reconstruct" =>  new Approximation(FPABVEmptyApp)
      case "ijcar-node-by-node" => new Approximation(IJCARSmallFloatsNodeByNodeApp)
      case "ijcar-no-reconstruct" => new Approximation(IJCARSmallFloatsEmptyapp)
      case _ => throw new Exception("Unsupported approximation: \"" + str + "\"")
    }
  } 
                         
  var approximation = "ijcar"
  var backend = "z3"
  var validator = "z3"

  def getApproximation = registeredApproximations(approximation.toLowerCase())

  def getBackendSolver = registeredSolvers(backend.toLowerCase())

  def getValidator = registeredSolvers(validator.toLowerCase())

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


object UppSAT {
  
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
    println("\t -t=NUM - set a soft timeout in seconds. Soft means that timeout is checked between iterations only.")
    
    
  }
  
  def printHelpInfo() = {
    println("Input file missing. Call uppsat -h or uppsat -help for usage help.")
  }

  /**
    * Prints description of approximations
    */
  def printDescriptions() = {
    val maxLength = approximationDescriptions.map(_._1.length).max + 3
    val title = "Approximation:"
    println(title + " "*(maxLength - title.length) + "Description:")
    println("-"*(maxLength + approximationDescriptions.map(_._2.length).max))
    for ((app, desc) <- approximationDescriptions) {
      println(app + " "*(maxLength - app.length) + desc)
    }
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
               
        case dashPattern() => printUsage()
        case _ => true
      }
      false
  }
  
  def main_aux(args : Array[String]) : Answer = {
    import java.io._
    import scala.collection.JavaConversions._
    

    globalOptions.reset()
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

