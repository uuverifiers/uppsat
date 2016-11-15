package uppsat;

trait SMTSolver {
  def solve(formula : String) : Boolean
  def getModel(formula : String, extractSymbols : List[String]) : Map[String, String]
}
