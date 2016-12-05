package uppsat.solver;

import java.io.ByteArrayInputStream;
import scala.sys.process.stringToProcess
import uppsat.solver._

object Z3Solver extends SMTSolver {
  def runSolver(formula : String) = {
    import sys.process._
    val is = new ByteArrayInputStream(formula.getBytes("UTF-8"))
    ("z3 -in -smt2" #< is) !! 
  }
 
  
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head.trim()
    if (result != "sat")
      throw new Exception("Trying to get model from non-sat result (" + result + ")")
    
    val model = (extractSymbols zip lines.tail).toMap
    Some(model)
  }
  
  def getModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = runSolver(extendedFormula)
    parseOutput(result, extractSymbols).get    
  }
  
  def solve(formula : String) : Boolean = {
    println(formula)
    val result = runSolver(formula)  
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }

}
