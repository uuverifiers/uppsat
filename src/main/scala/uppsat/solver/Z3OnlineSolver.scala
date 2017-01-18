package uppsat.solver;

import java.io.ByteArrayInputStream;
import sys.process._
import scala.sys.process.stringToProcess
import uppsat.solver._
import java.io.BufferedReader;
import java.io.InputStreamReader;
import uppsat.Timer

class Z3OnlineException(msg : String) extends Exception("Z3 error: " + msg)

// Starts process at 

class Z3OnlineSolver extends SMTSolver {

  def z3print(str : String) =
    println("[Z3] " + str)
  // Starting solver...
  val process = Runtime.getRuntime().exec("z3 -in")
  z3print("[Started process: " + process)
  val stdin = process.getOutputStream ()
  val stderr = process.getErrorStream ()
  val stdout = process.getInputStream ()  
  
  def runSolver(formula : String) = Timer.measure("Z3OnlineSolver.runSolver") {
    z3print("Sending input: " + formula)    
    stdin.write((formula + "\n").getBytes());
    stdin.flush();    
    
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    var result = None : Option[String]    

    val satPattern = "sat".r
    val errorPattern = ".*error.*".r

    var line = None : Option[String]
    println("Z3 says :")
    var i = 1
    while (result.isEmpty) {
      line = Option(outReader.readLine())
      println(i + " : " + line)
      i += 1
      line.get match { //TODO: Remove
        case satPattern => println("Found sat") // Skip over the sat result of the empty check-sat call
        case errorPattern() => throw new Exception("Z3 error: " + line.get)
        case other => println("Non-sat result")
                      result = Some(other)
      }    
    }
    result.get
  }
 
  def reset = { //TODO
    
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
