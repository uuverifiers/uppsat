package uppsat.solver;

trait SMTSolver {
  def checkSat(formula : String) : Boolean
  def evaluate(formula : String) : String
  def getStringModel(formula : String, extractSymbols : List[String]) : Map[String, String]
  def getAnswer(formula : String) : String 
}
