package uppsat.solver;

import java.io.{BufferedReader, FileNotFoundException, InputStreamReader};

import uppsat.globalOptions
import uppsat.Timer
import uppsat.Timer.TimeoutException

class Z3Solver(val name : String = "Z3",
               val checkSatCmd : String = "(check-sat)")
    extends SMTSolver {

  case class Z3Exception(msg : String) extends Exception("Z3 error: " + msg)

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

    try {
	    val process = Runtime.getRuntime().exec(cmd)
	    print("Started process: " + process)
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
		      case toPattern() => throw new TimeoutException("Z3Solver.evaluate")
		      case other => result = result ++ List(other)
	      }
	      line = outReader.readLine()
	    }
	    process.waitFor();
	    val exitValue = process.exitValue()

	    result.mkString("\n")
    } catch {
	    case e : java.io.IOException => {
        // Most times we get "broken pipe" because of timeout, so if deadline is
        // violated, lets throw timeout exception instead.
        globalOptions.checkTimeout()

        // If it wasn't timeout, probably its because z3 binary is not found
        val msg = "(probably) z3 binary not found"
        throw new Z3Exception(msg)
      }
    }
  }

  def parseOutput(output : String,
                  extractSymbols : List[String])
      : Option[Map[String, String]] = {
    val lines = output.split("\n")
    lines.head.trim() match {
      case "timeout" => throw new TimeoutException("Z3solver")
      case "sat" => Some((extractSymbols zip lines.tail).toMap)
      case "unsat" => None
      case result => {
        // Make sure this is not timeout related.
        globalOptions.checkTimeout()
        val msg = "Trying to get model from non-sat result (" + output + ")"
        throw new Z3Exception(msg)
      }
    }
  }

  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula + "\n" + checkSatCmd +
      (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = evaluate(extendedFormula)
    parseOutput(result, extractSymbols)
  }

  def checkSat(formula : String) : Boolean = {
    val result = evaluate(formula + "\n" + checkSatCmd)
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => {
        val msg = "Unexpected result: " + str
        throw new Z3Exception(msg)
      }
    }
  }

  def getAnswer(formula : String) : String = {
    val result = evaluate(formula + "\n" + checkSatCmd)
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => {
        val msg = "Unexpected result: " + str
        throw new Z3Exception(msg)
      }
    }
  }
}
