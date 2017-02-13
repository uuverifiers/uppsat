package uppsat

import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.theory.Theory
import uppsat.approximation.Approximation
import ast.AST
import uppsat.solver.SMTSolver
import uppsat.solver.SMTTranslator
import uppsat.solver.Z3OnlineSolver
import uppsat.theory.FloatingPointTheory.FPVar
import uppsat.ast._
import uppsat.globalOptions._

object ModelReconstructor {
  //type Model = Map[Path, AST]
  
  class Model() {
    var variableValuation : Map[ConcreteFunctionSymbol, AST] = Map()
    var subexprValuation : Map[Path, AST] = Map()
    
      
    def getModel : Map[ConcreteFunctionSymbol, AST] = {
      variableValuation
    }
    
    def getDefinedAssignmentsFor(ast : AST) = {
      for ( n <- ast.iterator if n.symbol.theory.isVariable(n.symbol) && contains(n)) yield {
        val value = this(n)
        (n.symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
      }
    }
    
    def getAssignmentsFor(ast : AST)   = {
      for ( n <- ast.iterator if n.symbol.theory.isVariable(n.symbol)) yield {
        val value = this(n)
        (n.symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
      }      
    }
    
    def set(ast : AST, value : AST) : Unit = {
      if (contains(ast)){
        throw new Exception("Reassigning  a model value")
      }
      
      if (ast.symbol.sort != ast.symbol.sort)
        throw new Exception("Model is not typed corectly! " + ast.symbol + " / " + value.symbol)
      
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation = variableValuation + (symbol -> value)
            case _ if (children.length == 0) =>
              ()
            case _ => 
              subexprValuation = subexprValuation + (path -> value)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
      ()
    }
    
    def containsVariable( symbol : ConcreteFunctionSymbol) : Boolean = {
      variableValuation.contains(symbol)
    }
    def contains(ast : AST) : Boolean = {
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation.contains(symbol)
            case _ if (children.length == 0) =>
              true
            case _ => 
              subexprValuation.contains(path)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
    }
    
    def apply(ast : AST) : AST = {
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation(symbol)
            case _ if (children.length == 0) =>
              ast
            case _ => 
              subexprValuation(path)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
    }
  }
  
  var onlineSolver = None : Option[SMTSolver]
  
  def startOnlineSolver() = {
    onlineSolver = Some(new Z3OnlineSolver)
    onlineSolver.get.asInstanceOf[Z3OnlineSolver].init
  }
  
  
  def stopOnlineSolver() = {
    onlineSolver.get.asInstanceOf[Z3OnlineSolver].stopSolver()    
  }
  
  def resetOnlineSolver() = {
    onlineSolver.get.asInstanceOf[Z3OnlineSolver].reset
  }
 
  def valAST(ast: AST, assignments: List[(String, String)], theory : Theory, solver : SMTSolver) : Boolean = {
    val translator = new SMTTranslator(theory)
    val smtVal = translator.translate(ast, false, assignments)
    debug("valAST...")
    debug(smtVal)
    val result = solver.checkSat(smtVal)
    debug("\t" + result)
    result
  }
  
  def evalAST(ast : AST, theory : Theory) : AST = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    else
      resetOnlineSolver()
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evaluate(ast)
    val answer = onlineSolver.get.asInstanceOf[Z3OnlineSolver].evaluateExpression(formula)
    ast.symbol.sort.theory.parseLiteral(answer.trim())    
  }
  
  def evalAST(ast : AST, answer : ConcreteFunctionSymbol, assignments : List[(ConcreteFunctionSymbol, AST)], theory : Theory) : Option[AST] = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    else
      resetOnlineSolver()
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evaluateSubformula(ast, answer, assignments)
     
    val res = onlineSolver.get.asInstanceOf[Z3OnlineSolver].evaluate(formula, List(answer))
    if (!res.isEmpty)
      Some (answer.sort.theory.parseLiteral(res.head.trim()))
    else
      None        
  }
  
  def getValue(constraint : AST, unknown: AST, theory : Theory) : AST = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evalExpression(constraint, unknown)
    resetOnlineSolver()
    val res = onlineSolver.get.evaluate(formula)
    unknown.symbol.sort.theory.parseLiteral(res.trim())    
  }
  
  
  // Reconstruction patterns
  def reconstructNodeByNode(ast : AST, decodedModel : Model, nodeByNodeHook : (Model, Model, AST) => Model) : Model = {
    val reconstructedModel = new Model()    
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, nodeByNodeHook)
    reconstructedModel
  }
}