package uppsat.solver;

import java.io.ByteArrayInputStream;
import uppsat.globalOptions
import scala.sys.process.stringToProcess
import uppsat.solver._
import uppsat.Timer
import uppsat.Timer.TimeoutException
import sys.process._
import java.io.BufferedReader;
import java.io.InputStreamReader;


class Z3Exception(msg : String) extends Exception("Z3 error: " + msg)

class Z3Solver(name : String = "Z3", val checkSatCmd : String = "(check-sat)") extends SMTSolver {
  var silent = true
  
  def setSilent(b : Boolean) = {
    silent = b
  }
  
  def z3print(str : String) =
    if (!silent)
      println("[Z3] " + str)
    
  def evaluate(formula : String) = Timer.measure("Z3Solver.runSolver") {
    import sys.process._
    
    globalOptions.verbose("Using Z3 with seed: " + globalOptions.RANDOM_SEED)
    val z3Binary = "z3 sat.random_seed=" + globalOptions.RANDOM_SEED
    
    val cmd = 
      if (globalOptions.DEADLINE.isDefined) {
        val dlf = ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt
        z3Binary + " -T:" + dlf + " -in -smt2"
      } else {
        z3Binary + " -in -smt2"
      }       
          
    
    println(cmd)
    val process = Runtime.getRuntime().exec(cmd)
    z3print("[Started process: " + process)
    val stdin = process.getOutputStream ()
    val stderr = process.getErrorStream ()
    val stdout = process.getInputStream ()
    
    stdin.write((formula + "\n(exit)\n").getBytes("UTF-8"));    
    stdin.close();
    
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    var result = List() : List[String] 
    val toPattern = ".*timeout.*".r
    // TODO: Maybe restore the errorPattern but excluding model calls
    
    
    var line = outReader.readLine()
    while (line != null) {
      line match { 
//        case errorPattern() =>  {
//          import java.io._
//          val pw = new PrintWriter(new File("error.smt2"))
//          pw.write(formula)
//          pw.close
//          throw new Z3Exception(line)
//        }
        case toPattern() => throw new TimeoutException("Z3Solver.evaluate")
        case other => result = result ++ List(other)        
      }
      line = outReader.readLine()
    }
    process.waitFor();
    val exitValue = process.exitValue()
//    if (exitValue != 0) {
//      println(result.mkString("\n"))
//      throw new Exception("[" + name + "] Exited with a non-zero value")
//    }
    result.mkString("\n")
  }
 
  
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    lines.head.trim() match {
      case "timeout" => throw new TimeoutException("Z3solver")
      case "sat" => Some((extractSymbols zip lines.tail).toMap)
      case "unsat" => None
      case result => throw new Exception("Trying to get model from non-sat result (" + output + ")") 
    }
  }
  
  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula + "\n" + checkSatCmd + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = evaluate(extendedFormula)
    parseOutput(result, extractSymbols)   
  }
  
  def checkSat(formula : String) : Boolean = {
    val result = evaluate(formula + "\n" + checkSatCmd)  
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexpected result: " + str)
    }
  }

  def getAnswer(formula : String) : String = {
    val result = evaluate(formula + "\n" + checkSatCmd)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => throw new Exception("Unexpected result: " + str)
    }
  }

}
