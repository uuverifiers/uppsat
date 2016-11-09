package uppsat;

object main {
  
//
//  object FPFactory extends IndexedSortFactory { 
//    case class FPSort(eBits : Int, sBits : Int) extends IndexedSort {
//      val name = "Floating Point (" + eBits + ", " + sBits + ")"
//      val toSMTLib = "(_ FloatingPoint " + eBits + " " + sBits +")"
//      val getFactory = FPFactory
//    }
//
//    val rank = 2
//    def apply(idx : Seq[BigInt]) = {
//      val eBits = idx(0).toInt
//      val sBits = idx(1).toInt
//      // Anonymous class, notation!
//      // Maybe use HashTable to store and re-use
//      new FPSort(eBits, sBits)
//    }
//  }
// 
//
//  object RoundingModeSort extends ConcreteSort {
//    val name = "RoundingMode"
//    val toSMTLib = "RoundingMode"
//  }
//  
  
  // TODO: Change factory to something else?
//  class FPOpFactory(op : String) extends IndexedFunctionSymbolFactory {
//    val thisFactory = this
//    
//    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
//    case class FPAddFunctionSymbol(arg1 : Sort, arg2 : Sort, res : Sort) extends IndexedFunctionSymbol {
//      val sort = res
//      val name = "Floating Point Addition with " + sort
//      val toSMTLib = "fp.add"
//      val args = List(RoundingModeSort, arg1, arg2)
//      val getFactory = thisFactory
//    }
//
//    val rank = 1
//    override def apply(sorts : Seq[Sort]) = {
//      op match {
//        // TODO: Pass integers instead of sorts?
//        case "fp.add" => new FPAddFunctionSymbol(sorts(0), sorts(1), sorts(2)) 
//      }
//      
//    }
//    
//    // TODO: Unapply should check if the argument symbol is of a instance fpfunctionsymbol and then pick it apart
//    // def unapply(FunctionSymbol : TypedFunctionSymbol) 
//    
//  }

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
    
//    val fp2_2 = FPFactory(List(2, 2))
//    println("fp2_2: (" + fp2_2.getClass + ") = " + fp2_2)
//    val fpAddFactory = new FPOpFactory("fp.add")
//    val fpAdd2_2 = fpAddFactory(List(fp2_2, fp2_2, fp2_2))
//    println("fpAdd2_2: (" + fpAdd2_2.getClass + ") = " + fpAdd2_2)
  ()
  }
}
