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
  
  
  def integer() = {
    import uppsat.IntegerTheory._
    import uppsat.BooleanTheory._
    
    val x = new IntVar("x")
    val y = new IntVar("y")
    
    (x === ( y - 4)) & ( (x + y) === 6)
    
  }
  
  
  def main(args : Array[String]) = {
    val formula= integer()
    //val extractSymbols = defSyms.map(_.toString).toList
    println("<<<SMT Formula>>>")
    val enc = new Encoder[Int]
    val pmap = new PrecisionMap[Int]
    for ( n <- formula.nodes)
      pmap.update(n, 100)
    val encFormula = enc.encode(formula, pmap)
    
    val translator = new SMTTranslator(IntegerTheory)
    val SMT = translator.translate(formula)
    println(SMT)
    println("<<<Encoded SMT Formula>>>")
    val SMT2 = translator.translate(encFormula)
    println(SMT2)
//    val result = Z3Solver.solve(formula, extractSymbols)
//    if (result.isDefined)
//      println("Model found: " + result.get)
//    else
//      println("No model...")
  ()
  }
}
