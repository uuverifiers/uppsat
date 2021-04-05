package uppsat

import uppsat.ast._
import uppsat.globalOptions._
import uppsat.precision.PrecisionMap.Path
import uppsat.solver.{SMTSolver, SMTTranslator, Z3OnlineSolver}
import uppsat.theory.Theory

/** The ModelReconstructor reconstructs a full-scale model from a smaller model.
  *
  *
  */
object ModelEvaluator {

  case class ModelReconstructorException(msg : String) extends
      Exception("ModelReconstructor: " + msg)

  /** A Model which is incrementally (re-)constructed.
    *
    *
    */
  class Model() {

    // Mapping variables to concrete values
    var variableValuation : Map[ConcreteFunctionSymbol, AST] = Map()

    // Mapping subexpressions to values
    var subexprValuation : Map[Path, AST] = Map()

    def toMap : Map[ConcreteFunctionSymbol, AST] = variableValuation

    /** Returns the assignments of all variables in ast.
      *
  		* @param ast The assignment of all variables in ast are extracted
  		* @param incomplete If incomplete is set to true, unassigned variables
  		* found in @param ast are ignored (default false)
      *
  		* @return One pair of strings for each variable in ast (one pair of
  		* strings for each assigned variable in ast if incomplete)
      */
     def variableAssignments(ast : AST, incomplete : Boolean = false) = {
      for (n <- ast.iterator if n.symbol.theory.isVariable(n.symbol) &&
           (!incomplete || containsVariable(n.symbol))) yield {
        val value = this(n)
        (n.symbol.toString(), value.symbol.theory.symbolToSMTLib(value.symbol))
      }
    }

    /** Replaces the assignment of ast with value.
      *
      *  Replaces, in the model, the assignment of ast to instead be equal to
      *  value. If ast was previously unassigned it is just added.
      *
  		* @param ast The key to which value is assigned
  		* @param value The value which is assigned to key
      *
      * @throws ModelReconstructorException if {@code ast} and {code value} have
      * different sorts
      */
    def overwrite(ast : AST, value : AST) : Unit = {
      if (ast.symbol.sort != value.symbol.sort) {
        val msg = "Incorrectly typed model: " + ast.symbol + "/" + value.symbol
        throw new ModelReconstructorException(msg)
      }

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
  		* @param ast The key to which value is assigned
  		* @param value The value which is assigned to key
      *
      * @throws ModelReconstructorException if {@code ast} is already assigned
      * or if {@code ast} and {code value} have different sorts
      */
    def set(ast : AST, value : AST) : Unit = {
      if (contains(ast)) {
        val msg = "Model value " + ast + " already assigned"
        throw new ModelReconstructorException(msg)
      }
      overwrite(ast, value)
    }

    /** Checks whether model contains variable.
      *
  		* @param variable Variable to check
  		* @return True if model contains variable otherwise false
      * @throws ModelReconstructorException if {@code variable} is not a
      * variable
      */
    def containsVariable(variable : ConcreteFunctionSymbol) = {
      if (!variable.theory.isVariable(variable)) {
        val msg = "Variable is not a variable: " + variable
        throw new ModelReconstructorException(msg)
      }

      variableValuation.contains(variable)
    }

    /** Checks whether model contains subexpression
      *
  		* @param path Path of subexpression
  		* @return True if model contains subexpression otherwise false
      * variable
      */
    def containsSubexpr(path : Path) : Boolean =
      subexprValuation.contains(path)


    /** Checks whether model contains variable or subexpression.
      *
  		* @param ast AST to check
  		* @return True if model contains ast otherwise false
      * @throws ModelReconstructorException if ast is non-AST model value
      */
    def contains(ast : AST) : Boolean = {
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) =>
              containsVariable(symbol)
            case _ if (children.length == 0) =>
              // Non-variable leaf without children is constant literal
              true
            case _ =>
              containsSubexpr(path)
          }
        }
        case _ => {
          val msg = "Requesting a non-AST model value!"
          throw new ModelReconstructorException(msg)
        }
      }
    }

    /** Assigned value of ast.
      *
  		* @param ast Key of desired value.
      * @throws ModelReconstructorException if model doesn't contain ast
      */
    def apply(ast : AST) : AST = {
      if (!contains(ast)) {
        val msg = "Model doesn't contain value: " + ast
        throw new ModelReconstructorException(msg)
      }

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

  // Online solver used for handling SMT queries. Z3 by default.
  var onlineSolver = None : Option[SMTSolver]
  /** Access the online solver as {@code Z3OnlineSolver}.
    */
  def getz3() = onlineSolver.get.asInstanceOf[Z3OnlineSolver]

  /** Starts an online solver (default Z3).
    *
    */
  def startOnlineSolver() = {
    onlineSolver = Some(new Z3OnlineSolver)
    getz3().init()
  }

  /** Stops the online solver.
    *
    * @throws ModelReconstructorException if solver hasn't been created yet
    */
  def stopOnlineSolver() = {
    if (onlineSolver.isEmpty) {
      val msg = "Online Solver hasn't been created."
      throw new  ModelReconstructorException(msg)
    }

    getz3().stopSolver()
  }

  /** Resets state of the online solver.
    *
    * @throws ModelReconstructorException if solver hasn't been created yet
    */
  def resetOnlineSolver() = {
    if (onlineSolver.isEmpty) {
      val msg = "Online Solver hasn't been created."
      throw new  ModelReconstructorException(msg)
    }

    getz3().reset
  }


  /** Check satisfiability of a formula.
    *
    * Evaluates the formula in {@code ast}, under {@code assignments} with
    * {@code theory} using {@code solver}.
    *
    * @param ast Formula to be evaluated
    * @param assignments Assignments to variables
    * @param theory Theory to be used
    * @param solver SMT solver to use
    * @return True if formula is satisfiable otherwise false
    */
  def valAST(ast: AST,
             // assignments: List[(String, String)],
              assignments : List[(ConcreteFunctionSymbol, AST)],
             theory : Theory,
             solver : SMTSolver) : Boolean = {
    val translator = new SMTTranslator(theory)

    // TODO (ptr): We should lift out this assignments thing and create a proper
    // datatype (maybe we have)? Which could have the "stringify" function, I am
    // sure this is not the only place it is used.
    val stringAssignments =
      for ((symbol, value) <- assignments) yield {
        (symbol.toString(), value.symbol.theory.symbolToSMTLib(value.symbol))
      }

    val smtFormula = translator.translate(ast, false, stringAssignments)
    solver.checkSat(smtFormula)
  }

  /** Compute the value of an ast.
    *
    * Compute the value of the formula in {@code ast} with {@code theory} using
    * an online solver.
    *
    * @param ast Formula to be evaluated
    * @param theory Theory to be used
    * @return Value of root node in {@code ast}
    */
   def evalAST(ast : AST, theory : Theory) : AST = {
     if (onlineSolver.isEmpty)
       startOnlineSolver()
     else
       // TODO (ptr): Do we need to restart solver here? Perhaps we can ignore
       // doing this? Danger is if previous assignments is still remaining, but
       // we can maybe argue that the new assignments should override those.
       resetOnlineSolver()

     val translator = new SMTTranslator(theory)
     val formula = translator.evaluate(ast)
     val answer =
       getz3().evaluateExpression(formula)
     ast.symbol.sort.theory.parseLiteral(answer.trim())
   }


  // TODO (ptr): What does function do?
  // answer is the value in the model we are looking for
  /** ??????????
    *
    * ??????????????
    *
    * @param ast ???????????
    * @param answer ??????????
    * @param assignments ??????????
    * @param theory ??????????????
    * @return ???????????
    */
  def evalAST(ast : AST,
              answer : ConcreteFunctionSymbol,
              assignments : List[(ConcreteFunctionSymbol, AST)],
              theory : Theory) : Option[AST] = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    else
      resetOnlineSolver()

    val translator = new SMTTranslator(theory)
    val formula = translator.evaluateSubformula(ast, answer, assignments)

    val res =
      getz3().evaluate(formula, List(answer))
    if (!res.isEmpty)
      Some (answer.sort.theory.parseLiteral(res.head.trim()))
    else
      None
  }

  // Reconstruction patterns
  def reconstructNodeByNode(ast : AST,
                            decodedModel : Model,
                            hook : (Model, Model, AST) => Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, hook)
    reconstructedModel
  }
}
