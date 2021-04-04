package uppsat.solver;

import java.io.{BufferedReader, File, InputStreamReader, PrintWriter};

import uppsat.globalOptions
import uppsat.Timer.TimeoutException
import uppsat.Timer
import sys.process._


class MathSatSolver(val name : String = "MathSAT", params : String = "")
    extends SMTSolver {

  case class MathSatException(msg : String)
    extends Exception("MathSAT error: " + msg)

  def evaluate(formula : String) = Timer.measure("MathSatSolver.runSolver") {

    val mathsatBin = "mathsat"

    val cmd =
      if (globalOptions.DEADLINE.isDefined) {
        val dlf = ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt
        "timeout -s 2 " + dlf + "s " + mathsatBin + " -model -stats " + params
      } else {
      	mathsatBin + " -model -stats " + params
      }

    val process = Runtime.getRuntime().exec(cmd)

    print("Started process: " + process)
    val stdin = process.getOutputStream ()
    val stderr = process.getErrorStream ()
    val stdout = process.getInputStream ()

    print(formula)
    stdin.write((formula + "\n(check-sat)\n(exit)\n").getBytes("UTF-8"));
    stdin.close();

    val outReader = new BufferedReader(new InputStreamReader (stdout))
    val errReader = new BufferedReader(new InputStreamReader (stdout))

    var result = List() : List[String]
    val errorPattern = ".*error.*".r
    val toPattern = ".*Interrupted by signal.*".r

    var line = outReader.readLine()
    while (line != null) {
      line match {
        case toPattern() => {
          while (line != null) {
            println(line)
            line = outReader.readLine()
          }
          throw new TimeoutException("MathsatSolver.evaluate")
        }
        case errorPattern() =>  {
          val pw = new PrintWriter(new File("error.smt2"))
          pw.write(formula)
          pw.close
          throw new MathSatException(line)
        }
        case other => result = result ++ List(other)
      }
      line = outReader.readLine()
    }
    process.waitFor();
    val exitValue = process.exitValue()
    exitValue match {
      case 0 => result.mkString("\n")
      case 124 => {
        // Timeout
        println(result.mkString("\n"))
        throw new TimeoutException("MathsatSolver.evaluate")
      }
      case ev => {
        println(result.mkString("\n"))
        val msg = "[" + name + "] Exited with a non-zero value (" +
          exitValue + ") running: " + cmd
        throw new MathSatException(msg)
      }
    }
  }

  def valueExtractor(lit : String) : (String, String) = {
    val valuePattern = """[(][\s(]*([\S]+)[\s(]+([^)]+)[)\s]+""".r
    val statPattern0 = ";; statistics".r
    val statPattern1 = "\\(".r
    val statPattern2 = ":.*".r
    val statPattern3 = "\\)".r

    lit.trim match {
      case valuePattern(variable, value) => (variable, value)
      case statPattern0() => ("", "")
      case statPattern1() => ("", "")
      case statPattern2() => ("", "")
      case statPattern3() => ("", "")
      case _ => throw new MathSatException("Error matching value " + lit)
    }
  }
  def parseOutput(output : String,
                  extractSymbols : List[String]) :
      Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head.trim()
    result match {
      case "sat" => {
        if (result != "sat") {
          val msg = "Trying to get model from non-sat result (" + result + ")"
          throw new MathSatException(msg)
        }
        print("Model:\n\t" + lines.mkString("\n\t"))

        // Head of output is "sat"
        val model =
          lines.tail.map(valueExtractor(_)).filter(_._1 != "").toMap
        Some(model)
      }
      case "unsat" => None
      case other => {
        val msg = "Strange Mathsat return value: " + other
        throw new MathSatException(msg)
      }
    }
  }

  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val result = evaluate(formula)
    parseOutput(result, extractSymbols)
  }

  def checkSat(formula : String) : Boolean = {
    val result = evaluate(formula)
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => {
        val msg = "Unexpected result: " + str
        throw new MathSatException(msg)
      }
    }
  }

  def getAnswer(formula : String) : String = {
    val result = evaluate(formula)
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => {
        val msg = "Unexpected result: " + str
        throw new MathSatException(msg)
      }
    }
  }
}
