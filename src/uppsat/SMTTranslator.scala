package uppsat

import scala.collection.mutable.{Set, Map, MutableList}
import uppsat.PrecisionMap.Path
import uppsat.ModelReconstructor.Model

class SMTTranslator(theory : Theory) {
  //var definedSymbols = Set() : Set[ConcreteFunctionSymbol]
  
  // TODO: HACK
  //val symbolToAST = Map() : Map[ConcreteFunctionSymbol, AST]
  var nextAST = 0
  val pathToId = Map() : Map[Path, String]
  val IdToPaths = Map() : Map[String, List[Path]]
  val astSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]
  
  def translateASTaux(ast : AST, path : Path) : String = {
     // TODO: Make this proper?  
     ast match {
       case Leaf(symbol) => {
         // TODO: Refine this...
         val thisAST = symbol.theory.toSMTLib(symbol)
         if (!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {           
           val astId = thisAST
           pathToId += path -> astId
           IdToPaths += astId -> (path :: (IdToPaths.getOrElse(astId, List())))
           
           val newSymbol = thisAST
           val newSort  = symbol.sort.theory.toSMTLib(symbol.sort)
           val symbolAssertion = "(= " + newSymbol + " " + thisAST + ")"    
           astSymbols += ((newSymbol, newSort))           
         }
         thisAST
       }
       
       case AST(symbol, children) => {
           val fun = symbol.theory.toSMTLib(symbol) 
           val args = for ((c, i) <- children zip children.indices) yield translateASTaux(c, i :: path)
           val thisAST = "(" + fun + " " + args.mkString(" ") + ")"
           
           // Create extra-symbol that contains the value of this ast
           val astId = ast.symbol.toString + nextAST.toString
           pathToId += path -> astId
           IdToPaths += astId -> (path :: (IdToPaths.getOrElse(astId, List())))
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
  
  def translateAST(ast : AST) = translateASTaux(ast, List())
  
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
    pathToId.clear()
    IdToPaths.clear()
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
    pathToId.clear()
    IdToPaths.clear()
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
  def getASTModel(ast : AST, stringModel : scala.collection.immutable.Map[String, String]) : Model = {
    (for ((k, v) <- stringModel) yield {
      val paths = IdToPaths(k)
      // TODO: only one path to check?
      val valAST = ast(paths.head).symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
//      println("getASTModel..." + k + " ... " + paths.mkString(", ") + " -> " + valAST)
      val newMappings = (for (p <- paths) yield p -> valAST)
      newMappings
    }).flatten.toMap
  }
}