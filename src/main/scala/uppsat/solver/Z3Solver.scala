package uppsat.solver;

import java.io.ByteArrayInputStream;
import scala.sys.process.stringToProcess
import uppsat.solver._

class Z3Exception(msg : String) extends Exception("Z3 error: " + msg)

object Z3Solver extends SMTSolver {

  def runSolver(formula : String) = {
    import sys.process._
    
    val stdout = new StringBuilder
    val stderr = new StringBuilder    
    val is = new ByteArrayInputStream(formula.getBytes("UTF-8"))
    val status = "z3 -in -smt2" #< is ! ProcessLogger(str => stdout append (str + "\n"), str => stderr append (str + "\n"))
    if (status != 0) {
      import java.io._
      val pw = new PrintWriter(new File("error.smt2"))
      pw.write(formula)
      pw.close
      throw new Z3Exception(stdout.toString)
    }
    stdout.toString
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
    val result = runSolver(formula)  
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }

  def getAnswer(formula : String) : String = {
    val result = runSolver(formula)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }

}
