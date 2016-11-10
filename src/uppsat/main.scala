package uppsat;

object main {
  def boolean() = {    
    import uppsat.BooleanTheory._
    
    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue
   
    val f = a & (!b & (t & (!c)))
    val translator = new SMTTranslator(BooleanTheory)
    val SMT = translator.translate(f)
    println(SMT)
  }
  
  
  def integer() : (String, Set[ConcreteFunctionSymbol]) = {
    import uppsat.IntegerTheory._
    import uppsat.BooleanTheory._
    
    val x = new IntVar("x")
    val y = new IntVar("y")
    
    val f = (x === ( y - 4)) & ( (x + y) === 6)
    val translator = new SMTTranslator(IntegerTheory)
    val SMT = translator.translate(f)
    (SMT, translator.getDefinedSymbols)
  }
  def main(args : Array[String]) = {
    val (formula, defSyms) = integer()
    val extractSymbols = defSyms.map(_.toString).toList
    println("<<<SMT Formula>>>")
    println(formula)
    val result = Z3Solver.solve(formula, extractSymbols)
    if (result.isDefined)
      println("Model found: " + result.get)
    else
      println("No model...")
  ()
  }
}
