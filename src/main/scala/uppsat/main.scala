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
  var DEBUG = false
  var DEADLINE : Option[Long] = None
  var STARTTIME : Option[Long] = None
  var PARANOID = false
  
  var chosenBackend = 0
  
  val REG_SOLVERS = List( Z3Solver, MathSatSolver, MathSatACDCLSolver)
  val REG_APPROXS = List(   new PostOrderNodeBasedApproximation(IJCARSmallFloatsApp),
                            new AnalyticalFramework(FxPntSmallFloatsApp))
  var chosenApproximation = 1
  
  def getApproximation = REG_APPROXS(chosenApproximation)
  
  def getBackendSolver = REG_SOLVERS(chosenBackend)
  
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
  
  def boolean() = {

    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue

//    val rootNode = a & (!b & (t & (!c)))
    val rootNode = AST(naryConjunction(3), List(a, b, c))
    val translator = new SMTTranslator(BooleanTheory)
    (rootNode, List(a, b, c), translator, EmptyApproximation)

  }

  def integer() = {

    val x = new IntVar("x")
    val y = new IntVar("y")

    val rootNode = (x === (y - 4)) & ((x + y) === 6)
    (rootNode, List(x, y), new SMTTranslator(RealTheory), IntApproximation)
  }
  
  
  def real() = {

    val x = new RealVar("x")
    val y = new RealVar("y")

    val rootNode = (x === (y - NumeralToAST(4))) & ((x + y) === DecimalToAST(6.5))
    (rootNode, List(x, y), new SMTTranslator(RealTheory), IntApproximation)
  }
  
  def contradiction() = {
    val x = new IntVar("x")
    val y = new IntVar("y")

    val rootNode = (x + 3 === y + 5)
    (rootNode, List(x, y), new SMTTranslator(RealTheory), EmptyApproximation)
  }    
  
//  def floatingpoint() = {
//    implicit val rmm = RoundToPositive
//    implicit val fpsort = FPSortFactory(List(8,24))
//    
//    val x = FPVar("x")
//    val y = FPVar("y")
//    val c : AST = 1.75f
//    val rootNode = (x + 1.75f === y) & (x === 2f)
//    (rootNode, List(x, y), new SMTTranslator(FloatingPointTheory), SmallFloatsApproximation)
//  }
  
  
//    val (formula, vars, translator, approximation) = real()
//    println("-----------------------------------------------")
//    println("Formula ")
//    println("-----------------------------------------------")
//    formula.prettyPrint
//    
//    ApproximationSolver.loop(formula, translator, approximation)
//    println("Running time: -- ms")
//    
  def main(args: Array[String]) = {
    verbose("Args: " + args.mkString("|"))
    main_aux(args) match {
      case _ : Sat => System.exit(10)
      case Unsat   => System.exit(20)
      case Unknown => System.exit(30)        
    }
  }    
  
  def printUsage() = {
    println("Usage: uppsat [-options] input file")
    println("Options:")
    println("\t-v - verbose output")
    println("\t-d - debugging output")
    println("\t-p - run a second check using z3 to verify internal queries")
    println("\t-b=NUM - use one of the following backends:")
    println("\t\t 0 : Z3 (default)")
    println("\t\t 1 : MathSat")
    println("\t\t 2 : MathSat(ACDCL)")
    println("\t -a=NUM - use one of the following approximations:")
    println("\t\t 0 : Smallfloats (node based reconstruction)")
    println("\t\t 1 : Smallfloats (fixpoint based reconstruction)")
    println("\t -t=NUM - set a soft timeout in seconds. Soft means that timeout is checked between iterations only.")
    
  }
  
  def printHelpInfo() = {
    println("Input file missing. Call uppsat -h or uppsat -help for usage help.")
  }
  
  def parseArgument( arg : String) : Unit = {
      val timeoutPattern = "-t=([0-9.]+)".r
      val appPattern = "-a=([0-9.])".r
      val backend = "-b=([0-9.]+)".r
      val dashPattern = "-.*".r
      arg match {
        
        case "-v" => globalOptions.VERBOSE = true
                     
        case "-d" => globalOptions.DEBUG = true
        
        case "-p" => globalOptions.PARANOID =  true
        
        case "-h" | "-help" => printUsage()
        
        case backend(i) => 
           i.toInt match {
             case 0 | 1 | 2 => globalOptions.chosenBackend = i.toInt
             case _ => throw new Exception("Unsupported backend solver")
           }
        
        case appPattern(i) => globalOptions.chosenApproximation = i.toInt
        
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
      
    val nonOptions = args.filterNot(_.startsWith("-"))  
    
    if (nonOptions.isEmpty) {
       printHelpInfo()
       Unknown
    } else {
      val file = nonOptions.toList(0)
      val reader = () => new java.io.BufferedReader (new java.io.FileReader(new java.io.File(file)))            
      val l = new smtlib.Yylex(reader())
      val p = new smtlib.parser(l)
      val script = p.pScriptC
      Timer.reset
      Timer.measure("main") {
        Interpreter.reset()
        Interpreter.interpret(script)
      }
      println(Timer.toString())
      Interpreter.myEnv.result
    }
  }
}

