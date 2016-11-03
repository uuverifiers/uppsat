package uppsat;

object main {

  // Examples
  object IntSort extends ConcreteSort {
    val name = "Integer"
    val toSMTLib = "Int"
  }
  
  

  object FPFactory extends IndexedSortFactory { 
    case class FPSort(eBits : Int, sBits : Int) extends IndexedSort {
      val name = "Floating Point (" + eBits + ", " + sBits + ")"
      val toSMTLib = "(_ FloatingPoint " + eBits + " " + sBits +")"
      val getFactory = FPFactory
    }

    val rank = 2
    def apply(idx : Seq[BigInt]) = {
      val eBits = idx(0).toInt
      val sBits = idx(1).toInt
      // Anonymous class, notation!
      // Maybe use HashTable to store and re-use
      new FPSort(eBits, sBits)
    }
  }

  // Singleton?
  object IntAdd extends ConcreteFunctionSymbol {
    val name = "Integer Addition"
    val toSMTLib = "+"
    val args = List(IntSort, IntSort)
    val sort = IntSort
  }

  object RoundingModeSort extends ConcreteSort {
    val name = "RoundingMode"
    val toSMTLib = "RoundingMode"
  }
  
  
  class FPOpFactory(op : String) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // Ask Philipp: Should this be outside for purposes of pattern-matching?
    case class FPAddFunctionSymbol(arg1 : Sort, arg2 : Sort, res : Sort) extends IndexedFunctionSymbol {
      val sort = res
      val name = "Floating Point Addition with " + sort
      val toSMTLib = "fp.add"
      val args = List(RoundingModeSort, arg1, arg2)
      val getFactory = thisFactory
    }

    val rank = 1
    override def apply(sorts : Seq[Sort]) = {
      op match {
        case "fp.add" => new FPAddFunctionSymbol(sorts(0), sorts(1), sorts(2)) 
      }
      
    }
    
    // Ask Philipp: Should this be in the FPFunctionSymbol
    // def unapply(FunctionSymbol : TypedFunctionSymbol) 
    
  }

  def main(args : Array[String]) = {
    println("Testing")

    val fp2_2 = FPFactory(List(2, 2))
    println("fp2_2: (" + fp2_2.getClass + ") = " + fp2_2)
    val fpAddFactory = new FPOpFactory("fp.add")
    val fpAdd2_2 = fpAddFactory(List(fp2_2, fp2_2, fp2_2))
    println("fpAdd2_2: (" + fpAdd2_2.getClass + ") = " + fpAdd2_2)
  }
}
