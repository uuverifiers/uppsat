package uppsat;

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


object main {
  
  def boolean() = {

    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue

    val f = a & (!b & (t & (!c)))
    val translator = new SMTTranslator(BooleanTheory)
    val SMT = translator.translate(f)
    println(SMT)
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
//    val (formula, vars, translator, approximation) = contradiction()
//    println("-----------------------------------------------")
//    println("Formula ")
//    println("-----------------------------------------------")
//    
//    ApproximationSolver.loop(formula, translator, approximation)
//    println("Running time: -- ms")
    
    import smtlib._
    import smtlib.Absyn._
    import java.io._
    import scala.collection.JavaConversions._
    import uppsat.parser._
    
    
    val filename = "mule.smt2";
    val reader = () => new java.io.BufferedReader (new java.io.FileReader(new java.io.File (filename)))
    println(reader)
    val l = new smtlib.Yylex(reader())
    val p = new parser(l)
    val script = p.pScriptC
    val result = Interpreter.interpret(script)
//    import uppsat.parser.smttest
//    smttest.test("simplefp.smt2")
  }    
}
