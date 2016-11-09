package uppsat;

trait SMTSolver {
  def solve(formula : String, defSyms : List[String]) : Option[Map[String, String]]
}
