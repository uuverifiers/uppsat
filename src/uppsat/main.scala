package uppsat;

import uppsat.main.FPFactory.FPSort

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
  
  
  // TODO: Change factory to something else?
  class FPOpFactory(op : String) extends IndexedFunctionSymbolFactory {
    val thisFactory = this
    
    // TODO: This should only be Symbol, since each instance of the factory will have it's own instance of the class
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
        // TODO: Pass integers instead of sorts?
        case "fp.add" => new FPAddFunctionSymbol(sorts(0), sorts(1), sorts(2)) 
      }
      
    }
    
    // TODO: Unapply should check if the argument symbol is of a instance fpfunctionsymbol and then pick it apart
    // def unapply(FunctionSymbol : TypedFunctionSymbol) 
    
  }

  def boolean() = {
    //Theory
    // Sort
    // Symbol, consts, funs, variables
    
    
    // TODO: Make function for generating these classes.
    
    //Sort
    object BooleanSort extends ConcreteSort {
      val name = "Boolean"
      val toSMTLib = "Bool"
    }
    
    // Constants   
    case object BoolTrue extends ConcreteFunctionSymbol {
      val name = "true"
      val toSMTLib = "true"  
      override val args = List()
      override val sort = BooleanSort
    }
    
    // Symbols, conjunction and negation
    case object BoolConjunction extends ConcreteFunctionSymbol {
      val name = "conjunction"
      val toSMTLib = "and"  
      override val args = List(BooleanSort, BooleanSort)
      override val sort = BooleanSort
    }
    
    case object BoolNegation extends ConcreteFunctionSymbol {
      val name = "negation"
      val toSMTLib = "not"  
      override val args = List(BooleanSort)
      override val sort = BooleanSort
    }
    
    // Make regular class; id is not support to be the identifier
    case class BoolVar(id : String) extends ConcreteFunctionSymbol {
      val name = id
      val toSMTLib = id
      override val args = List()
      override val sort = BooleanSort
    }
    
    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue
    
    import uppsat.AST._

    // TODO: Make things nicer using infix operators and more.
    val C = LeafNode(c)
    val notC = InternalNode(BoolNegation, List(C))
    val T = LeafNode(t)
    val TandC = InternalNode(BoolConjunction, List(T, notC))
    val B = LeafNode(b)
    val notB = InternalNode(BoolNegation, List(B))
    val notBandTandC = InternalNode(BoolConjunction, List(notB, TandC))
    val A = LeafNode(a)
    val f = InternalNode(BoolConjunction, List(A, notBandTandC))
    println(f)
  }
  
  def main(args : Array[String]) = {
    println("Testing")
    
    boolean()
    val fp2_2 = FPFactory(List(2, 2))
    println("fp2_2: (" + fp2_2.getClass + ") = " + fp2_2)
    val fpAddFactory = new FPOpFactory("fp.add")
    val fpAdd2_2 = fpAddFactory(List(fp2_2, fp2_2, fp2_2))
    println("fpAdd2_2: (" + fpAdd2_2.getClass + ") = " + fpAdd2_2)
  }
}
