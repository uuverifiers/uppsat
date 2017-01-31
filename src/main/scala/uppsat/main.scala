package uppsat;

import uppsat.precision.PrecisionMap
import uppsat.theory.BooleanTheory._
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

object globalOptions {
  // FLAGS
  var VERBOSE = false
  var DEBUG = false

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
    (rootNode, List(x, y), new SMTTranslator(IntegerTheory), IntApproximation)
  }
  
  def contradiction() = {
    val x = new IntVar("x")
    val y = new IntVar("y")

    val rootNode = (x + 3 === y + 5)
    (rootNode, List(x, y), new SMTTranslator(IntegerTheory), IntApproximation)
  }    
  
  def floatingpoint() = {
    implicit val rmm = RoundToPositive
    implicit val fpsort = FPSortFactory(List(8,24))
    
    val x = FPVar("x")
    val y = FPVar("y")
    val c : AST = 1.75f
    val rootNode = (x + 1.75f === y) & (x === 2f)
    (rootNode, List(x, y), new SMTTranslator(FloatingPointTheory), SmallFloatsApproximation)
  }
  
  def main(args: Array[String]) = {
//    val (formula, vars, translator, approximation) = boolean()
//    println("-----------------------------------------------")
//    println("Formula ")
//    println("-----------------------------------------------")
//    formula.prettyPrint
//    
//    ApproximationSolver.loop(formula, translator, approximation)
//    println("Running time: -- ms")
    
    verbose("Args: " + args.mkString("|"))
    
    import java.io._
    import scala.collection.JavaConversions._

    val file =
      if (args.isEmpty)
        "debug.smt2"
      else
        args.toList(0)
        
    val reader = () => new java.io.BufferedReader (new java.io.FileReader(new java.io.File(file)))            
    val l = new smtlib.Yylex(reader())
    val p = new smtlib.parser(l)
    val script = p.pScriptC
    Timer.measure("main") {
      val result = Interpreter.interpret(script)
    }
    verbose(Timer.toString())
    
    import uppsat.ApproximationSolver.Answer
    Interpreter.result match {
      case _ : ApproximationSolver.Sat => System.exit(10)
      case ApproximationSolver.Unsat   => System.exit(20)
      case ApproximationSolver.Unknown => System.exit(30)        
    }
  }    
}
