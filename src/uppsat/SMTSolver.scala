package uppsat;

trait SMTSolver {
  def solve(formula : String) : Boolean
}
