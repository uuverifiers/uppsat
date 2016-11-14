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
    def setPrecMap(p : Int) = {
      for ( n <- formula.nodes)
        pmap.update(n, p)      
    }

    setPrecMap(1)
    
    val encFormula = enc.encode(formula, pmap)
    val translator = new SMTTranslator(IntegerTheory)
    val SMT = translator.translate(formula)
    println(SMT)
    println("<<<Encoded SMT Formula>>>")
    val SMT2 = translator.translate(encFormula)
    println(SMT2)
    

//    var precision = 0
//    var result = false
//    while (!result && precision < 10) {
//      precision += 1
//      setPrecMap(precision)
//      println("Trying precision " + precision)
//      val pFormula = enc.encode(formula, pmap)
//      val pSMT = translator.translate(pFormula)
//      result = Z3Solver.solve(pSMT)
//    }
//    
//    if (result) {
//      val pFormula = enc.encode(formula, pmap)
//      val pSMT = translator.translate(pFormula)      
//      println("Model found: " + Z3Solver.getModel(pSMT, translator.getDefinedSymbols.toList.map(_.toString)))
//    } else {
//      println("No model found...")
//    }
  }
}
