package uppsat

import scala.collection.mutable.{Set, Map, MutableList}

class SMTTranslator(theory : Theory) {
  //var definedSymbols = Set() : Set[ConcreteFunctionSymbol]
  
  // TODO: HACK
  //val symbolToAST = Map() : Map[ConcreteFunctionSymbol, AST]
  var nextAST = 0
  val astToId = Map() : Map[AST, String]
  val IdToAST = Map() : Map[String, AST]
  val astSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]
  
  def translateAST(ast : AST) : String = {
     // TODO: Make this proper?  
     ast match {
       case Leaf(symbol) => {
         // TODO: Refine this...
         val thisAST = symbol.theory.toSMTLib(symbol)
         if (!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {           
           val astId = thisAST
           astToId += ast -> astId
           IdToAST += astId -> ast
           
           val newSymbol = thisAST
           val newSort  = symbol.sort.theory.toSMTLib(symbol.sort)
           val symbolAssertion = "(= " + newSymbol + " " + thisAST + ")"    
           astSymbols += ((newSymbol, newSort))           
         }
         thisAST
       }
       
       case AST(symbol, desc) => {
           val fun = symbol.theory.toSMTLib(symbol) 
           val args = desc.map(translateAST)
           val thisAST = "(" + fun + " " + args.mkString(" ") + ")"
           
           // Create extra-symbol that contains the value of this ast
           val astId = ast.symbol.toString + nextAST.toString
           astToId += ast -> astId
           IdToAST += astId -> ast
           nextAST += 1             
           
           val newSymbol = astId
           val newSort  = symbol.sort.theory.toSMTLib(symbol.sort)
           val symbolAssertion = "(= " + newSymbol + " " + thisAST + ")" 
           astSymbols += ((newSymbol, newSort))
           symbolAssertions += symbolAssertion
           
           thisAST
       }
       
     }
  }
  
  def declarations(symbols : List[ConcreteFunctionSymbol]) = {
    (for (s <- symbols) yield
      s.theory.declarationToSMTLib(s)).filter(_ != "").mkString("\n")
  }
  
  def symDecs= {
    astSymbols.toList.map(x => x match { case (sym, sort) => "(declare-fun " + sym + " () " + sort + ")"}).mkString("\n")
  }
  
  def symAsserts= {
    symbolAssertions.map("(assert " + _ + ")").mkString("\n")
  }
  
  def translate(ast : AST) : String = {
//    definedSymbols.clear()
    nextAST = 0
    astToId.clear()
//    symbolToAST.clear()
    astSymbols.clear()
    symbolAssertions.clear()
    
    val assertions = "(assert " + translateAST(ast) + ")"
    
    header + "\n" +
//    declarations(definedSymbols.toList) + "\n" +
    symDecs + "\n" +
    symAsserts + "\n" + 
    assertions + "\n" +
    footer
  }
  
// TODO: What is a meaningful way to do this (sometimes we want to assert root ast, sometimes don't)  
def translateNoAssert(ast : AST) : String = {
//    definedSymbols.clear()
    nextAST = 0
    astToId.clear()
//    symbolToAST.clear()
    astSymbols.clear()
    symbolAssertions.clear()
    
   val assertions = "(assert " + translateAST(ast) + ")"

    
    header + "\n" +
//    declarations(definedSymbols.toList) + "\n" +
    symDecs + "\n" +
    symAsserts + "\n" + 
    footer
  }  
  
  def header = {
    theory.SMTHeader
  }
  
  def footer = {
    "(check-sat)"
  }
  
  //    def getDefinedSymbols = definedSymbols.toSet ++ astSymbols.map(_._1)
  def getDefinedSymbols = astSymbols.map(_._1)  

  // TODO: Change ...mutable.Map to MMap
  def getASTModel(model : scala.collection.immutable.Map[String, String]) : scala.collection.immutable.Map[AST, AST] = {
    (for ((k, v) <- model) yield {
      val ast = IdToAST(k)
      val valAST = ast.symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
      ast -> valAST
    }).toMap
  }
}