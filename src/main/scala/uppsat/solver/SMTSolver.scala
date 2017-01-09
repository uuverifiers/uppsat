package uppsat.solver;

trait SMTSolver {
  def solve(formula : String) : Boolean
  def runSolver(formula : String) : String
  def getModel(formula : String, extractSymbols : List[String]) : Map[String, String]
  def getAnswer(formula : String) : String 
}
