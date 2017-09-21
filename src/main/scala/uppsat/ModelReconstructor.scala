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

/** The ModelReconstructor which reconstructs a full-scale model from a smaller model
 *
 *  
 */
object ModelReconstructor {
 
  case class ModelReconstructorException(msg : String) extends Exception("ModelReconstrutor Exception: " + msg)
  
  /** A Model which is incrementally (re-)constructed
   *
   *  
   */  
  class Model() {
    var variableValuation : Map[ConcreteFunctionSymbol, AST] = Map()
    var subexprValuation : Map[Path, AST] = Map()
    
    def getModel : Map[ConcreteFunctionSymbol, AST] = variableValuation
    
    /** Returns the assignments of all variables in ast
  		  @param ast The assignment of all variables in ast are extracted
  		  @param incomplete If incomplete is set to true, unassigned variables found in @param ast are ignored (default false)
  		  
  		  @return One pair of strings for each variable in ast (one pair of strings for each assigned variable in ast if incomplete)
     */      
    def variableAssignments(ast : AST, incomplete : Boolean = false) = {
      for ( n <- ast.iterator if n.symbol.theory.isVariable(n.symbol) && (!incomplete || contains(n))) yield {
        val value = this(n)
        (n.symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
      }
    }
    
    /** Replaces the assignment of ast with value.
     *  
     *  Replaces, in the model, the assignment of ast to instead be equal to value. If ast was previously unassigned it is just added.
     *  
  		  @param ast The key to which value is assigned.
  		  @param value The value which is assigned to key.
     */      
    def overwrite(ast : AST, value : AST) : Unit = {
      if (ast.symbol.sort != ast.symbol.sort)
        throw new ModelReconstructorException("Incorrectly typed model: " + ast.symbol + " / " + value.symbol)

      ast match {
        case AST(symbol, path, children) => {
          if (symbol.theory.isVariable(symbol))
              variableValuation += symbol -> value
          else if (children.length == 0)
            ()
          else 
            subexprValuation += path -> value
        }
      }
    }
    
     /** Assigns ast with value.
     *    
  		  @param ast The key to which value is assigned.
  		  @param value The value which is assigned to key.
  		  @throws ModelReconstructorException if ast is already assigned.
     */      
    def set(ast : AST, value : AST) : Unit = {
      if (contains(ast))
        throw new ModelReconstructorException("Model value " + ast + " already assigned")     
      overwrite(ast, value)
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
    
     /** Returns assigned value of ast.
     *    
  		  @param ast Key of desired value.
  		  @return Assigned value of ast.
     */       
    def apply(ast : AST) : AST = {
      ast match {
        case AST(symbol, path, children) => {
          if (symbol.theory.isVariable(symbol)) {
              variableValuation(symbol)
          } else if (children.length == 0) {
            // Non-variable leaf without children is constant literal
            ast
          } else {
            subexprValuation(path)
          }
        }
      }
    }
    
    override def toString() = {
      variableValuation.mkString("\n")
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
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evaluate(ast)
    val answer = onlineSolver.get.asInstanceOf[Z3OnlineSolver].evaluateExpression(formula)
    ast.symbol.sort.theory.parseLiteral(answer.trim())    
  }
  
  // answer is the value in the model we are looking for
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