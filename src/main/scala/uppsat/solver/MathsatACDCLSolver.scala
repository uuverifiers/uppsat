package uppsat.solver;

import java.io.ByteArrayInputStream;
import scala.sys.process.stringToProcess
import uppsat.solver._
import uppsat.Timer
import sys.process._
import java.io.BufferedReader;
import java.io.InputStreamReader;


class MathSatACDCLException(msg : String) extends Exception("MathSatACDCLACDCL error: " + msg)

object MathSatACDCLSolver extends SMTSolver {
  var silent = true
  
  def setSilent(b : Boolean) = {
    silent = b
  }
  
  def mathsatPrint(str : String) =
    if (!silent)
      println("[MathSatACDCL] " + str)
    
  def evaluate(formula : String) = Timer.measure("MathSatACDCLSolver.runSolver") {
    import sys.process._
  
    val process = Runtime.getRuntime().exec("mathsat -theory.fp.mode=2 -model")
    mathsatPrint("[Started process: " + process)
    val stdin = process.getOutputStream ()
    val stderr = process.getErrorStream ()
    val stdout = process.getInputStream ()
    
    mathsatPrint(formula)
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
          throw new MathSatACDCLException("MathSatACDCL error : " + line)
        }
        case other => result = result ++ List(other)        
      }
      line = outReader.readLine()
    }
    process.waitFor();
    val exitValue = process.exitValue()
    if (exitValue != 0) 
      throw new Exception("[MathSatACDCL] Exited with a non-zero value")
    result.mkString("\n")
  }
 
  def valueExtractor(lit : String) : (String, String) = {
    val valuePattern = """[(][\s(]*([\S]+)[\s(]+([^)]+)[)\s]+""".r
    
    lit.trim match {
      case valuePattern(variable, value) => (variable, value)
      case _ => throw new MathSatACDCLException("Error matching value " + lit)
                
    }
  }
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head.trim()
    if (result != "sat")
      throw new Exception("Trying to get model from non-sat result (" + result + ")")
    
    mathsatPrint("Model:\n\t" + lines.mkString("\n\t"))
    val model = lines.tail.map(valueExtractor(_)).toMap //.head is "sat"
    Some(model)
  }
  
  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula // + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
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
