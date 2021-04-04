package uppsat.solver;


import java.io.{BufferedReader, InputStreamReader}
import uppsat.Timer
import uppsat.Timer.TimeoutException
import uppsat.ast.ConcreteFunctionSymbol


class Z3OnlineSolver(val name : String = "Z3Online",
                     checkSatCmd : String = "(check-sat)\n") extends SMTSolver {

  class Z3OnlineException(msg : String) extends Exception("Z3 error: " + msg)
  
  val process = Runtime.getRuntime().exec("z3 -in")
  print("Started process: " + process)
  val stdin = process.getOutputStream ()
  val stderr = process.getErrorStream ()
  val stdout = process.getInputStream () 
  val outReader = new BufferedReader(new InputStreamReader (stdout))
  
  def init() = {
    val oldSilent = silent
    setSilent(true)
    val f = "(reset)\n(check-sat)\n"
    feedInput(f)
    val r = catchOutput(f) 
    r match { 
      case Some("sat") => ()
      case _ => {
        val msg = "Empty check-sat failed to return sat : " + r
        throw new Z3OnlineException(msg)
      }
    }
    setSilent(oldSilent)
  }
  
  def feedInput(f : String) = {
    print("Sending ... \n" + f)
    stdin.write((f+"\n").getBytes());
    stdin.flush();
  }
  
  def catchOutput(formula : String) = {
    var result = None : Option[String]    

    val errorPattern = ".*error.*".r
    val satPattern = "sat".r
    val unsatPattern = "unsat".r
    
    var line = None : Option[String]
    while (result.isEmpty) {
      line = Option(outReader.readLine())
      line match {
        case Some(errorPattern()) => 
          println(formula)
          throw new Z3OnlineException("Z3 error: " + line.get)
        case Some(other) => print("Collected : " + other)
                            result = Some(other)
        // If Z3 crashes (e.g., by timeout) without output:
        case None => result = Option("unknown")
      }    
    }
    result
  }
  
  def evaluate(formula : String) : String = {
    evaluate(formula + "\n" + checkSatCmd, List()).head
  }
  
  // Assumes a check-sat call has already been made
  def evalSymbol( symbol : ConcreteFunctionSymbol) = {
    val formula = "(eval " + symbol + ")" 
    feedInput(formula)
    catchOutput(formula)
  }
  
  // Evaluation of a an expression, should always result in a value
  def evaluateExpression(expression : String) =
    Timer.measure("Z3OnlineSolver.runSolver") {
    init
    print("Evaluating: \n" + expression)    
    feedInput(expression)
    catchOutput(expression).get 
  }
    
  def evaluate(formula : String,
               answers : List[ConcreteFunctionSymbol] = List())
      : List[String] = Timer.measure("Z3OnlineSolver.runSolver") {
    reset      
    feedInput(formula + "\n" + checkSatCmd)
    catchOutput(formula) match {
      case Some("sat") =>
        answers.map(evalSymbol(_)).collect { case Some(x) => x }
      case Some("unsat") =>
        List()
      case Some("unknown") =>
        List()
      case Some(s) =>
        throw new Z3OnlineException("Solver returned : " + s)
      case None =>
        throw new Z3OnlineException("Solver failed to return result")
    }
  }
  
  def reset = {
    val oldSilent = silent
    setSilent(true)
    feedInput("(reset)\n")
    setSilent(oldSilent)
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
        val msg = "Trying to get model from non-sat result (" + result + ")"
        throw new Z3OnlineException(msg)
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
        throw new Z3OnlineException(msg)
      }
    }
  }

  //Not used by the online solver
  def getAnswer(formula : String) : String = {
    val result = evaluate(formula + "\n" + checkSatCmd)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => {
        val msg = "Unexpected result: " + str
        throw new Z3OnlineException(msg)
      }
    }
  }
  
  def stopSolver() = {
    process.destroy()
    process.waitFor()
  }
}
