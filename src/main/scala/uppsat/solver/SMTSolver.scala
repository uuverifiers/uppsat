package uppsat.solver;

/** Interace for a back-end SMT solver. */
trait SMTSolver {
  def checkSat(formula : String) : Boolean
  def evaluate(formula : String) : String
  def getStringModel(formula : String,
                     extractSymbols : List[String])
      : Option[Map[String, String]]

  // TODO (ptr): What does this do?
  def getAnswer(formula : String) : String

  val name : String
  var silent = true
  def setSilent(b : Boolean) = silent = b
  def print(str : String) =
    if (!silent)
      println(s"[$name] $str")
}



