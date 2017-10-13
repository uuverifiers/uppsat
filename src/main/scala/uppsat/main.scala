package uppsat;

import uppsat.precision.PrecisionMap
import uppsat.theory.BooleanTheory._
import uppsat.theory.RealTheory._
import uppsat.theory._
import uppsat.ast._
import uppsat.parser._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.IntegerTheory._
import uppsat.solver._
import uppsat.approximation._
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.globalOptions._

import uppsat.ApproximationSolver.Answer
import uppsat.ApproximationSolver.Unknown
import uppsat.ApproximationSolver.Unsat
import uppsat.ApproximationSolver.Sat
import uppsat.ApproximationSolver.Answer

object globalOptions {
  // FLAGS
  var VERBOSE = false
  var STATS = false
  var MODEL = false
  var DEBUG = false
  var DEADLINE : Option[Long] = None
  var STARTTIME : Option[Long] = None
  var PARANOID = false
  
  
  
  val REG_SOLVERS = Map( "z3" -> new Z3Solver(),                           
                         "mathsat" -> new MathSatSolver(),
                         "acdcl" -> new MathSatSolver(" -theory.fp.mode=2 "),
                         "nlsat" -> new Z3Solver("NLSAT","(check-sat-using qfnra-nlsat)\n"))
                          
  val REG_APPROXS = Map( "ijcar" ->  new PostOrderNodeBasedApproximation(IJCARSmallFloatsApp),
                          "saturation" ->  new AnalyticalFramework(FxPntSmallFloatsApp),                            
                          "reals" ->  new PostOrderNodeBasedApproximation(FPARealApp),
                          "fixedpoint" ->  new PostOrderNodeBasedApproximation(FPABVApp),
                          "empty" -> EmptyApproximation)
                                            
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
  
  def checkTimeout : Boolean = {
    DEADLINE match {
      case None => true
      case Some(t) => System.currentTimeMillis() - STARTTIME.get < t
    }
  }
}


object main {
  
  def printUsage() = {
    println("Usage: uppsat [-options] input file")
    println("Options:")
    println("\t-v - verbose output")
    println("\t-s - print statistics")
    println("\t-m - print model (debug purposes)3")
    println("\t-d - debugging output")
    println("\t-p - run a second check using z3 to verify internal queries")
    println("\t-backend= - use one of the following backends:")
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
  
  def parseArgument( arg : String) : Unit = {
      val timeoutPattern = "-t=([0-9.]+)".r
      val appPattern = "-app=(\\S+)".r
      val backend = "-backend=(\\S+)".r
      val validator = "-validator=(\\S+)".r
      val dashPattern = "-.*".r
      arg match {
        case "-s" => globalOptions.STATS = true
        case "-m" => globalOptions.MODEL = true
        case "-v" => globalOptions.VERBOSE = true
        case "-d" => globalOptions.DEBUG = true
        case "-p" => globalOptions.PARANOID =  true
        case "-h" | "-help" => printUsage()
        
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
        
        case timeoutPattern(t) =>   globalOptions.DEADLINE = Some(t.toInt * 1000)
               
        case dashPattern() => printUsage()
        case _ => ()
      }
  }
  
  def main_aux(args : Array[String]) : Answer = {
    import java.io._
    import scala.collection.JavaConversions._
    
    globalOptions.STARTTIME = Some(System.currentTimeMillis())
    
    for (a <- args) yield {
      parseArgument(a)
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
      debug(Timer.toString())
      if (globalOptions.STATS)
        println(Timer.stats)
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
      Interpreter.myEnv.result
    }
  }
  
  def main(args: Array[String]) = {
    
    verbose("Args: " + args.mkString("|"))
    // TODO: (Aleks) Do we need these system exit codes? Usually non-zero means error I think?
    main_aux(args) match {
      case Sat(_) => System.exit(10)
      case Unsat   => System.exit(20)
      case Unknown => System.exit(30)        
    }
  }   
}

