package uppsat.solver

import scala.collection.mutable.{Set, Map => MMap, MutableList}
import uppsat.precision.PrecisionMap.Path
import uppsat.ModelReconstructor.Model
import scala.collection.mutable.{Map => MMap}
import uppsat.ast._
import uppsat.theory._

class SMTTranslator(theory : Theory) {
  // TODO: Should we make this immutable?  
  var nextAST = 0
  val IdToPaths = MMap() : MMap[String, List[Path]]
  val astSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]
  
  def translateASTaux(ast : AST) : String = {
     // TODO: Make this proper?  
     ast match {
       case Leaf(symbol, label) => {
         val smtSort  = symbol.sort.theory.toSMTLib(symbol.sort)           
         val smtSymbol = symbol.theory.toSMTLib(symbol)         

         if (!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {  
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
  
  def translateAST(ast : AST) = translateASTaux(ast)
  
  def declarations(symbols : List[ConcreteFunctionSymbol]) = {
    (for (s <- symbols) yield
      s.theory.declarationToSMTLib(s)).filter(_ != "").mkString("\n")
  }
  
  def symDecs =
    astSymbols.toList.map(x => x match { case (sym, sort) => "(declare-fun " + sym + " () " + sort + ")"}).mkString("\n")
  
  def symAsserts =
    symbolAssertions.map("(assert " + _ + ")").mkString("\n")
  
  def translate(ast : AST, assignments : List[(String, String)] = List()) : String = {
    nextAST = 0
    IdToPaths.clear()
    astSymbols.clear()
    symbolAssertions.clear()
    
    val astFormula = translateAST(ast)
    val assertions =
        "(assert " + astFormula + ")"
    
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
  
  def header = theory.SMTHeader
  
  def footer = "(check-sat)"
  
  def getDefinedSymbols = astSymbols.map(_._1)  

  def getModel(ast : AST, stringModel : Map[String, String]) : Model = {
    (for ((k, v) <- stringModel) yield {
      val paths = IdToPaths(k).filter(!_.isEmpty)
      // TODO: only one path to check?
      if (paths.isEmpty) { 
        List()
      } else {
        val valAST = ast(paths.head).symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
        (for (p <- paths) yield p -> valAST)
      }
    }).flatten.toMap
  }
}