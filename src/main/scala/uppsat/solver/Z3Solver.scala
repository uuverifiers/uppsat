package uppsat.solver;

import java.io.ByteArrayInputStream;
import scala.sys.process.stringToProcess
import uppsat.solver._
import uppsat.Timer
import sys.process._
import java.io.BufferedReader;
import java.io.InputStreamReader;


class Z3Exception(msg : String) extends Exception("Z3 error: " + msg)

object Z3Solver extends SMTSolver {
  var silent = true
  
  def setSilent(b : Boolean) = {
    silent = b
  }
  
  def z3print(str : String) =
    if (!silent)
      println("[Z3] " + str)
    
  def evaluate(formula : String) = Timer.measure("Z3Solver.runSolver") {
    import sys.process._
    
    val process = Runtime.getRuntime().exec("./z3 -in -smt2")
    z3print("[Started process: " + process)
    val stdin = process.getOutputStream ()
    val stderr = process.getErrorStream ()
    val stdout = process.getInputStream ()
    
    stdin.write((formula + "\n(exit)\n").getBytes("UTF-8"));    
    stdin.close();
    
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    var result = List() : List[String] 
    val errorPattern = ".*error.*".r
    
    var line = outReader.readLine()
    while (line != null) {
      line match { 
        case errorPattern() =>  {
          import java.io._
          val pw = new PrintWriter(new File("error.smt2"))
          pw.write(formula)
          pw.close
          throw new Z3Exception("Z3 error : " + line)
        }
        case other => result = result ++ List(other)        
      }
      line = outReader.readLine()
    }
    process.waitFor();
    val exitValue = process.exitValue()
    if (exitValue != 0) 
      throw new Exception("[Z3] Exited with a non-zero value")
    result.mkString("\n")
  }
 
  
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head.trim()
    if (result != "sat")
      throw new Exception("Trying to get model from non-sat result (" + result + ")")
    
    val model = (extractSymbols zip lines.tail).toMap
    Some(model)
  }
  
  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = evaluate(extendedFormula)
    parseOutput(result, extractSymbols).get    
  }
  
  def checkSat(formula : String) : Boolean = {
    val result = evaluate(formula)    
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }

  def getAnswer(formula : String) : String = {
    val result = evaluate(formula)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }

}
