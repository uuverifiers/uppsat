package uppsat;

import java.io.ByteArrayInputStream;

object Z3Solver extends SMTSolver {
  def runSolver(formula : String) = {
    import sys.process._
    val is = new ByteArrayInputStream(formula.getBytes("UTF-8"))
    ("z3 -in -smt2" #< is) !!
  }
 
  
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head
    if (result == "sat") {
      val model = (extractSymbols zip lines.tail).toMap
      Some(model)
    } else if (result == "unsat")
      None
    else
      throw new Exception("Failed to handle output from Z3: " + result)
  }
  
  def solve(formula : String, extractSymbols : List[String]) = {
    println("Trying to solve a simple SMT-formula")
    val extendedFormula = formula + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = runSolver(extendedFormula)
    parseOutput(result, extractSymbols)
  }

}
