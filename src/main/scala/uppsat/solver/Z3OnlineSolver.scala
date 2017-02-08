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
  var silent = true
  
  def setSilent(b : Boolean) = {
    silent = b
  }
  
  def z3print(str : String) =
    if (!silent)
      println("[Z3] " + str)
  
  // Starting solver...
  val process = Runtime.getRuntime().exec("z3 -in")
  z3print("[Started process: " + process)
  val stdin = process.getOutputStream ()
  val stderr = process.getErrorStream ()
  val stdout = process.getInputStream () 
  
  
  def init() = {
    stdin.write("(reset)\n(check-sat)\n".getBytes());
    stdin.flush();
    var result : Option[String] = None    
    var line = None : Option[String]
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    val satPattern = "sat".r
    while (result.isEmpty) {
      line = Option(outReader.readLine())
      line.get match { 
        case satPattern() => result = Some ("sat")
      }    
    }
    result.get
  }
  
  def evaluate(formula : String) = Timer.measure("Z3OnlineSolver.runSolver") {
    init
    z3print("Evaluating: " + formula)    
    stdin.write((formula + "\n").getBytes());
    stdin.flush();    
    
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    var result = None : Option[String]    

    val errorPattern = ".*error.*".r
    val satPattern = "sat".r
    val unsatPattern = "unsat".r
    
    var line = None : Option[String]
    while (result.isEmpty) {
      line = Option(outReader.readLine())
      line.get match { 
        case satPattern() => () // Ingore sat
        case unsatPattern() => result = Some("unsat") //HACK! Make this polite!!!!!
                               outReader.readLine() 
        case errorPattern() => 
          println(formula)
          throw new Exception("Z3 error: " + line.get)
        case other => result = Some(other)
      }    
    }
    result.get
  }

  
  def reset = {    
    stdin.write(("(reset)\n").getBytes());
    stdin.flush();
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

  //Not used by the online solver
  def getAnswer(formula : String) : String = {
    val result = evaluate(formula)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => throw new Exception("Unexpected sat/unsat result: " + str)
    }
  }
  
  def stopSolver() = {
    process.destroy()
    process.waitFor()
  }

}
