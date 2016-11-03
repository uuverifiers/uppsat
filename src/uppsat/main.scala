package uppsat;


object main {

  // Examples
  object IntSort extends ConcreteSort {
    override def name = "Integer"
    override def toSMTLib = "Int"
  }

  object FPFactory extends IndexedSortFactory {
    class FPSort(eBits : Int, sBits : Int) extends IndexedSort {
      override def name = "Floating Point (" + eBits + ", " + sBits + ")"
      override def toSMTLib = "(_ FloatingPoint " + eBits + " " + sBits +")"
      override def getFactory = FPFactory
    }

    override def rank = 2
    override def apply(idx : Seq[Int]) = {
      val eBits = idx(0)
      val sBits = idx(1)
      // Anonymous class, notation!
      // Maybe use HashTable to store and re-use
      new FPSort(eBits, sBits)
    }
  }

  // Singleton?
  object IntAdd extends ConcreteSymbol {
    override def name = "Integer Addition"
    override def toSMTLib = "+"
    override def args = List(IntSort, IntSort)
    override def sort = IntSort
  }

  object FPAddFactory extends SymbolFactory {
    class FPAddSymbol(sort_ : Sort) extends TypedSymbol {
      override def sort = sort_
      override def name = "Floating Point Addition with " + sort
      override def toSMTLib = "fp.add"
      override def args = List(sort, sort)
      override def getFactory = FPAddFactory
    }

    override def rank = 1
    override def apply(sorts : Seq[Sort]) = {
      val sort = sorts.head
      new FPAddSymbol(sort)
    }
    def apply(sort : Sort) : TypedSymbol = apply(List(sort))

  }

  def main(args : Array[String]) = {
    println("Testing")

    val fp2_2 = FPFactory(List(2, 2))
    println("fp2_2: (" + fp2_2.getClass + ") = " + fp2_2)
    val fpAdd2_2 = FPAddFactory(List(fp2_2))
    println("fpAdd2_2: (" + fpAdd2_2.getClass + ") = " + fpAdd2_2)
  }
}
