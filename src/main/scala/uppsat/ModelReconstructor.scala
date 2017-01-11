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

object ModelReconstructor {
  type Model = Map[Path, AST]
  
  var onlineSolver = None : Option[SMTSolver]
  
  def startOnlineSolver() = {
    onlineSolver = Some(new Z3OnlineSolver)
    onlineSolver.get.runSolver("(check-sat)\n(eval true)\n")
  }
  
  def valAST(ast: AST, assignments: List[(String, String)], theory : Theory, solver : SMTSolver) : Boolean = {
    val translator = new SMTTranslator(theory)
    val smtVal = translator.translate(ast, false, assignments)
    println("valAST...")
    println(smtVal)
    val result = solver.solve(smtVal)
    println("\t" + result)
    result
  }
  
  def evalAST(ast : AST, theory : Theory, solver : SMTSolver) : AST = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evaluate(ast)
    val answer = onlineSolver.get.runSolver(formula)
    println(answer)
    ast.symbol.sort.theory.parseLiteral(answer.trim())    
  }
}