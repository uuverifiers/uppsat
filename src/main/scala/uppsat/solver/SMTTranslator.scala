package uppsat.solver

import scala.collection.mutable.{Set, Map => MMap, MutableList}
import uppsat.precision.PrecisionMap.Path
import uppsat.ModelReconstructor.Model
import scala.collection.mutable.{Map => MMap}
import uppsat.ast._
import uppsat.theory._

class SMTTranslator(theory : Theory) {
  var nextAST = 0 // Counter to make node-names unique
  val IdToPaths = MMap() : MMap[String, List[Path]]
  val astSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]

  case class SMTTranslatorException(msg : String) extends Exception("SMTTranslatorException: " + msg) 

   
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
  
  /** Translates ast to SMT
   *  
   *  Takes ast and translates into a SMT formula. 
   *  Observe that auxiliary data structures are updated containing information to make the formula complete.  
   *  
		  @param ast The AST to be translated
		  
		  @return ast as a SMT-formula
  */ 
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
  
  def translate(ast : AST, noAssert : Boolean = false, assignments : List[(String, String)] = List(), noHeader : Boolean = false) : String = {
    val astFormula = translateAST(ast)
    val assertions = if (!noAssert) "(assert " + astFormula + ")" else ""
    
    val assig = for ((x, v) <- assignments) yield { 
      "(assert ( = " + x + " " + v + "))"
      }
     val head = if (!noHeader) header + "\n" else "" 
    
    head + 
    symDecs + "\n" +
    symAsserts + "\n" + 
    assertions + "\n" +
    assig.mkString("\n") + "\n" +
    footer
  }
  
  
  //Used by Fixpoint approximation
  def evaluateSubformula(ast : AST, answer : ConcreteFunctionSymbol, assignments : List[(ConcreteFunctionSymbol, AST)]) : String = {
    val strAssignments = for ((sym, value) <- assignments) yield {
      (sym.toString(), value.symbol.theory.toSMTLib(value.symbol))
    }
    translate(ast, false, strAssignments, true)     
  }
  
  def evalExpression(ast : AST, answer : AST, assignments : List[(ConcreteFunctionSymbol, AST)] = List()) : String = {
    val astFormula = translateAST(ast)
    val eval = "(assert " + astFormula + ")"
    //header + "\n" +
    //symDecs + "\n" + 
    "(declare-fun " + answer.symbol + " () " + answer.symbol.sort.theory.toSMTLib(answer.symbol.sort) +" )\n" +
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

  
  /** Converts a stringModel to a Model
   *  
   *  Converts a string representation of a model (mapping nodes to values) to a internal Model. 
   *  The stringModel is checked pair by pair (key, value), and for each key a corresponding node
   *  in ast is found (if several found the first one is taken) and is used as the key in the 
   *  resulting Model. Nodes created during encoding might not have a representative in the original ast (e.g. casts).
   *  
		  @param ast All nodes in ast are keys in the returned model.
		  @param stringModel is a given model based on the output from some external solver.
		  
		  @return A model where every value in stringModel is assigned to a respective key in ast.
  */        
  def getModel(ast : AST, stringModel : Map[String, String]) : Model = {
    val model = new Model()
    (for ((k, v) <- stringModel) {
      val paths = IdToPaths(k).filter(!_.isEmpty)
      // For every key in stringModel: if (i) there is a path to it,
      // make sure (ii) there is a node on such path in ast (iii) and add that
      // node to the model.
       
      if (!paths.isEmpty) {     
        val node = ast.getPathOrElse(paths.head)
        if (node.isEmpty)
          throw new SMTTranslatorException("Model key path not found in ast (ii)")
        
        val n = node.get
        val valAST = n.symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
        model.set(n, valAST)
      }
    })
    model
  }
    
}