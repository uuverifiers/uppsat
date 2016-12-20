package uppsat

import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.theory.Theory
import uppsat.approximation.Approximation
import ast.AST
import uppsat.solver.SMTSolver
import uppsat.solver.SMTTranslator

object ModelReconstructor {
  type Model = Map[Path, AST]
  
  def valAST(ast: AST, assignments: List[(String, String)], theory : Theory, solver : SMTSolver) : Boolean = {
    val translator = new SMTTranslator(theory)
    val smtVal = translator.translate(ast, false, assignments)
    solver.solve(smtVal)    
  }
  
  def evalAST(ast : AST, theory : Theory, solver : SMTSolver) : AST = {
    val translator = new SMTTranslator(theory)
    val formula = translator.evalExpression(ast)
    val answer = solver.getAnswer(formula)
    ast.symbol.sort.theory.parseLiteral(answer.trim())    
  }
}