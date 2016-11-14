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
    if (result != "sat")
      throw new Exception("Trying to get model from non-sat result (" + result + ")")
    
    val model = (extractSymbols zip lines.tail).toMap
    Some(model)
  }
  
  def getModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = runSolver(extendedFormula)
    parseOutput(result, extractSymbols)    
  }
  
  def solve(formula : String) : Boolean = {
    val result = runSolver(formula)  
    val retVal = result.split("\n").head
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexptected sat/unsat result: " + str)
    }
  }

}
