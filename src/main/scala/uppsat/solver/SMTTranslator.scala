package uppsat.solver

import scala.collection.mutable.{Set, Map => MMap, MutableList}
import uppsat.precision.PrecisionMap.Path
import uppsat.ModelReconstructor.Model
import scala.collection.mutable.{Map => MMap}
import uppsat.ast._
import uppsat.theory._

class SMTTranslator(theory : Theory) {  
  var nextAST = 0
  val IdToPaths = MMap() : MMap[String, List[Path]]
  val astSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]
  
  def translateASTaux(ast : AST) : String = { 
     ast match {
       case Leaf(symbol, label) => {
         val smtSort  = symbol.sort.theory.toSMTLib(symbol.sort)           
         val smtSymbol = symbol.theory.toSMTLib(symbol)         
         if (ast.isVariable) { //(!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {
           IdToPaths += smtSymbol -> (label :: (IdToPaths.getOrElse(smtSymbol, List())))
           astSymbols += ((smtSymbol, smtSort))
         }
         smtSymbol
       }
       
       case AST(symbol, label, children) => {
           val smtSymbol = symbol.theory.toSMTLib(symbol)
           val smtSort  = symbol.sort.theory.toSMTLib(symbol.sort)           
           val smtChildren = for ((c, i) <- children zip children.indices) yield translateASTaux(c)
           val smtAST = "(" + smtSymbol + " " + smtChildren.mkString(" ") + ")"
           
           // Create extra-symbol that contains the value of this ast
           val newSymbol = ast.symbol.toString + nextAST.toString
           IdToPaths += newSymbol -> (label :: (IdToPaths.getOrElse(newSymbol, List())))
           nextAST += 1             
           
           astSymbols += ((newSymbol, smtSort))
           symbolAssertions += "(= " + newSymbol + " " + smtAST + ")"
           
           smtAST
       }
       
     }
  }
  
  def translateAST(ast : AST) = {
    nextAST = 0
    IdToPaths.clear()
    astSymbols.clear()
    symbolAssertions.clear()    
    translateASTaux(ast)
  }
  
  def declarations(symbols : List[ConcreteFunctionSymbol]) = {
    (for (s <- symbols) yield
      s.theory.declarationToSMTLib(s)).filter(_ != "").mkString("\n")
  }
  
  def symDecs =
    astSymbols.toList.map(x => x match { case (sym, sort) => "(declare-fun " + sym + " () " + sort + ")"}).mkString("\n")
  
  def symAsserts =
    symbolAssertions.map("(assert " + _ + ")").mkString("\n")
  
  def translate(ast : AST, noAssert : Boolean = false, assignments : List[(String, String)] = List()) : String = {
    val astFormula = translateAST(ast)
    val assertions = if (!noAssert) "(assert " + astFormula + ")" else ""
    
    val assig = for ((x, v) <- assignments) yield { 
      "(assert ( = " + x + " " + v + "))"
      }
    header + "\n" +
    symDecs + "\n" +
    symAsserts + "\n" + 
    assertions + "\n" +
    assig.mkString("\n") + "\n" +
    footer
  }
  
  def evalExpression(ast : AST) : String = {
    val astFormula = translateAST(ast)
    val eval = "(assert (= answer " + astFormula + "))"
    header + "\n" +
    symDecs + "\n" + 
    "(declare-fun answer () " + ast.symbol.sort.theory.toSMTLib(ast.symbol.sort) +" )\n" +
    eval + "\n" +
    footer +  "\n" +
    "(eval answer)"
  }
  
  def evalExpression(ast : AST, answer : AST) : String = {
    val astFormula = translateAST(ast)
    val eval = "(assert " + astFormula + ")"
    //header + "\n" +
    symDecs + "\n" + 
    //"(declare-fun " + answer.symbol + " () " + answer.symbol.sort.theory.toSMTLib(answer.symbol.sort) +" )\n" +
    eval + "\n" +
    footer +  "\n" +
    "(eval " + answer.symbol + ")"
  }
  
  def evaluate(ast : AST) : String = {
    val astFormula = translateAST(ast)
    "(eval " + astFormula + ")" 
  }
  
  def evaluate(constraints : AST, answer : AST) : String = {
    val astFormula = translateAST(constraints)
    "(eval " + answer.symbol + ")" 
  }
  
  def header = theory.SMTHeader
  
  def footer = "(check-sat)"
  
  def getDefinedSymbols = astSymbols.map(_._1)  

  def getModel(ast : AST, stringModel : Map[String, String]) : Model = {
    val model = new Model()
    
    (for ((k, v) <- stringModel) {
      val paths = IdToPaths(k).filter(!_.isEmpty)
      // We only need to extract the value from one of the paths
      if (paths.isEmpty) { 
        List()
      } else {
        val valAST = ast(paths.head).symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
        val n = ast.getPath(paths.head)
        model.set(n, valAST)
        //(for (p <- paths) yield p -> valAST)
      }
    })
    model
  }
    
}