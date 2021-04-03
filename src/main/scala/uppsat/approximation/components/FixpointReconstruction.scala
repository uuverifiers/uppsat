package uppsat.approximation.components

import scala.collection.mutable.{ArrayBuffer, ArrayStack, HashMap,
  MultiMap, Queue, Set}

import uppsat.globalOptions._
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.Timer
import uppsat.approximation._
import uppsat.approximation.toolbox.Toolbox
import uppsat.ast._
import uppsat.precision.{PrecisionMap, PrecisionOrdering}
import uppsat.precision.PrecisionMap.Path
import uppsat.solver.Z3Solver
import uppsat.theory.Theory
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory._
import uppsat.solver.Z3OnlineSolver

// TODO (ptr): Add more details on fixpoint reconstruction

/** Fixpoint Reconstruction
  *
  *
  */
trait FixpointReconstruction extends ModelReconstruction {

  class FixpointException(msg : String)
      extends Exception("FixpointException: " + msg)

	/** Returns the assignment of one implied variable in ast (w.r.t. to
	  * candidateModel)
	 *
	 *  Assuming that ast w.r.t. candidateModel has exactly one undefined
	 *  variable, getImplication isolates this variable and by calling the
	 *  back-end solver retrieves a value and returns Some(variable, value) for
	 *  this pair. If no value is found None is returned (thus the candidateModel
	 *  is *not* a model for ast).
	 *
	 *  @param candidateModel Assignments of some values in ast.
	 *  @param ast The AST with exactly one undefined variable.
	 *
	 *  @return An assignment to the undefined variable in ast s.t. it is
	 *  compatible with candidateModel. None if none can be found.
 	 *
 	 */
  def getImplication(candidateModel : Model, ast : AST) : Option[(AST, AST)] = {
    val vars = ast.toList.filter(_.isVariable)
    val unknown =
      vars.filterNot(candidateModel.contains(_)).map(x => (x.symbol, x)).toMap

    unknown.toList match {
      case List((unkSymbol, unkAST)) => {
        verbose("Implication of  " +  unkSymbol + "\n\t" + ast.simpleString())
        val assertions =
          for ( v <- vars if(candidateModel.contains(v))) yield
            (v.symbol, candidateModel(v))

        ModelEvaluator.evalAST(ast, unkSymbol, assertions, inputTheory) match {
          case Some(res) => Some ((unkAST, res))
          case None => None
        }
      }
      case _ => {
        val msg =
          "getImplication assumes at most one unknown" + unknown.mkString(", ")
        throw new FixpointException(msg)
      }
    }
  }

  /** The number of variables in ast that are not defined in candidateModel
   *
   *  @param candidateModel Model (possibly) containing variable definitions
   *  @param ast AST (possibly) containing variables
   */
  def numUndefValues(candidateModel : Model, ast : AST) =
    ast.toList.filter((x:AST) =>
      x.isVariable && !candidateModel.contains(x)).map(_.symbol).distinct.length



  /** True if ast is a definition
   *
   *  An ast is a definition if it is an equation where one (or both) sides is a
   *  variable.
   *
   *  @param ast Formula to check
   *
   */
  // TODO (ptr): If we have a meta-equality we don't need to check for each
  // different theory.
  def isDefinition(ast : AST) : Boolean = {
    ast.symbol match {
      case pred : FloatingPointPredicateSymbol
          if (pred.getFactory == FPEqualityFactory) =>
        ast.children(0).isVariable || ast.children(1).isVariable
      case BoolEquality | RoundingModeEquality =>
        ast.children(0).isVariable || ast.children(1).isVariable
      case _ => false
    }
  }

  /** A Boolean symbol defined by {@code ast} if exists
    *
    * A symbol is defined if it is a single variable on one side of an equality.
    *
    * @param ast Formula to be checked for definition
    * @param polarity Should be true if formula is under a even number of
    * negations.
    * @return Some variable which is defined by {@code ast} if exists otherwise
    * None.
    *
    */
  def getBoolDefinitions(ast : AST, polarity : Boolean) : Option[(AST,AST)] = {
    (ast.symbol, polarity) match {
      case (BoolEquality, true) |
          (RoundingModeEquality, true) |
          (FPEqualityFactory(_), true) => {
        (ast.children(0).isVariable, ast.children(1).isVariable) match {
          case (true, _) => Some((ast.children(0), ast))
          case (_, true) => Some((ast.children(1), ast))
          case _ => None
        }
      }
      case _ => None
    }
  }

  /** All top-level subformulas which must be true for the formula to be true */
  def topLvlConjuncts(ast : AST) : Iterator[AST]= {
    ast.symbol match {
      case BoolConjunction | _ : NaryConjunction =>
        for (c <-  ast.children.iterator;
             d <- topLvlConjuncts(c)) yield d
      case _ => Iterator(ast)
    }
  }


  // TODO (Aleks): What is the difference between this and
  // retrieveCriticalAtoms?
  /** All critical atoms in {@code ast}.
    */
  def extractCriticalAtoms(ast : AST, decodedModel : Model) = {
    val (definitionAtoms, conjuncts) =
      topLvlConjuncts(ast).toList.partition(isDefinition(_))
    var definitions =
      for (a <- definitionAtoms; b <- getBoolDefinitions(a, true)) yield b
    val critical = new ArrayBuffer[AST]

    var todo = new Queue[AST]
    todo ++= conjuncts
    while (!todo.isEmpty) {
      for (c <- todo) {
        critical ++= Toolbox.retrieveCriticalAtoms(decodedModel)(c)
      }
      todo.clear()

      val vars = (for (c <- critical.iterator;
                       v <- c.iterator.filter(_.isVariable)) yield
                                                               v.symbol).toSet

      val (toBeAdded, toKeep) =
        definitions.partition((p) => vars.contains(p._1.symbol))
      todo ++= toBeAdded.map(_._2)
      definitions = toKeep
    }
    (definitions, critical, conjuncts) // TODO: Inspect the correct returns
  }

  /** Reconstruct formula {@code ast} using {@code decodedModel}
    */
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()

    verbose("Starting fixpoint reconstruction")
    val (definitions, critical, conjuncts) =
      extractCriticalAtoms(ast, decodedModel)
    verbose("Critical " + critical.mkString("\n\t"))
    verbose("Definitons : " + definitions.mkString("\n"))

    //TODO: Remove duplicate definitions
    //TODO: Cycle-breaking

    val varsToCritical =
      new HashMap[ConcreteFunctionSymbol, Set[AST]]
          with MultiMap[ConcreteFunctionSymbol, AST]

    (for (c <- critical.iterator; v <- c.iterator.filter(_.isVariable))
     yield (v.symbol, c)).foldLeft(varsToCritical){
      (acc, pair) => acc.addBinding(pair._1, pair._2)
    }

    //Fix-point computation
    var done = false
    var changed = false
    var iteration = 0

    val allVars =
      varsToCritical.keys.toList.sortWith((x,y) =>
        varsToCritical(x).size < varsToCritical(y).size)

    // Boolean variables can just be copied over
    for (v <- allVars if v.theory == BooleanTheory)
      copyFromDecodedModelIfNotSet(decodedModel, candidateModel, AST(v))

    var varDependency =
      new HashMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]]
          with MultiMap[ConcreteFunctionSymbol, ConcreteFunctionSymbol]

    for (c <- critical.toList if isDefinition(c)) {
      val lhs = c.children(0)
      if (lhs.isVariable && lhs.symbol.theory != BooleanTheory) {
        for (v <- c.children(1).iterator.filter(_.isVariable))
          varDependency.addBinding(lhs.symbol, v.symbol)
      }
      val rhs = c.children(0)
      if (rhs.isVariable && rhs.symbol.theory != BooleanTheory) {
        for (v <- c.children(0).iterator.filter(_.isVariable))
          varDependency.addBinding(rhs.symbol, v.symbol)
      }
    }

    val independentVars = Toolbox.topologicalSort(varDependency)

    // TODO: This is theory specific...
    // First migrate special values
    verbose("Migrating special values")

    for (v <- independentVars if v.sort.isInstanceOf[FPSort]) {
      val value = decodedModel(AST(v))
      value.symbol.asInstanceOf[IndexedFunctionSymbol].getFactory match {
        case FPSpecialValuesFactory(_) => {
          verbose("Migrating special value " + value)
          candidateModel.set(AST(v), value)
        }
        case _ => ()
      }
    }

    val vars =
      independentVars.filterNot(candidateModel.variableValuation.contains(_))
    verbose("Sorted variables :\n\t" + vars.mkString("\n\t"))

    while (!done) {
      iteration += 1
      verbose("=============================\nPatching iteration " + iteration)

      val implications =
        // TODO: reconsider the first condition
        critical.filter {x => x.children.length > 0 &&
                               isDefinition(x) &&
                               numUndefValues(candidateModel, x) == 1 }
                .sortBy(_.iterator.size)

      verbose("Implications(" + implications.length + "):")
      verbose(implications.map(_.simpleString()).mkString("\n\t"))
      verbose("**************************************************")
      changed = false

      // TODO: (Aleks) Some implications might become fully set? x = y*y?
      for (i <- implications if numUndefValues(candidateModel, i) == 1 )  {
        val imp = getImplication(candidateModel, i)

        imp match {
          case Some((node, value)) => {
            verbose("Inserting " + node.getSMT() + " -> " + value.getSMT())
            candidateModel.set(node, value)

            for ( crit <-  varsToCritical(node.symbol)
                if !candidateModel.contains(crit)
                && numUndefValues(candidateModel, crit) == 0) {
              // We will set the values only of the literals that
              // have not been evaluated yet and have no unknowns
              // Consider cascading expressions, do we need to watch all of them
              //evaluateNode(decodedModel, candidateModel, crit)

              // TODO: When does this fail?
              AST.postVisit(crit, candidateModel, candidateModel, evaluateNode)
              if (crit.symbol.sort == BooleanSort &&
                    candidateModel(crit) != decodedModel(crit)) {
                val str =
                  s"""Reconstruction fails for
${node.symbol} -> svalue
Implied by: ${i.simpleString()}
on literal
${crit.simpleString()}
DecodedModel ===================== ${decodedModel(crit)}
    ${decodedModel.variableAssignments(crit).mkString("\n\t")}
CandidateModel ===================== ${candidateModel(crit)}
    ${candidateModel.variableAssignments(crit).mkString("\n\t")}"""
                println(str)
              }
            }
            changed = true
          }
          case None => () // TODO: Model failed to be reconstructed
        }
      }

      // order 
      if (!changed) {
         verbose("No implications ... ")
        val undefVars =
          vars.filterNot(candidateModel.containsVariable(_)).toList
         if (undefVars.isEmpty) {
           verbose("No undefined variables \n Done supporting critical atoms.")

           // TODO: (Aleks) Do we actually care if the decoded model has extra
           // values?
           for ((variable, value) <- decodedModel.variableValuation
                 if (!candidateModel.contains(AST(variable)))) {
           }

           done = true
         } else {
           val chosen = undefVars.head // TODO: Call the method
           val node = AST(chosen)
           verbose("Copying from decoded model " + chosen + " -> " +
                     decodedModel(node).getSMT())

           var attempts = 0
           var done =  false
           var value = decodedModel(node)
           var violated : List[AST] = List()
           while (!done && attempts < 3) { // TODO: Tactic parameter
             attempts += 1

             candidateModel.overwrite(node, value)
             //TODO:  Construct one huge mega query to find this value?
             violated = List()
             for ( crit <-  varsToCritical(node.symbol)
                  if !candidateModel.contains(crit)
                  && numUndefValues(candidateModel, crit) == 0) {
                // We will set the values only of the literals that have not
                // been evaluated yet and have no unknowns Consider cascading
                // expressions, do we need to watch all of them

               //evaluateNode(decodedModel, candidateModel, crit)

               AST.postVisit(crit,
                             candidateModel,
                             candidateModel,
                             evaluateNode)

               if (crit.symbol.sort == BooleanSort &&
                     candidateModel(crit) != decodedModel(crit)) {
                 val str = """Migration violates:
${node.symbol} -> ${decodedModel(node)}
on literal
${crit.simpleString()}
DecodedModel
 ===================== ${decodedModel(crit)}
    ${decodedModel.variableAssignments(crit).mkString("\n\t")}
CandidateModel
 ===================== ${candidateModel(crit)}
    ${candidateModel.variableAssignments(crit).mkString("\n\t")}"""
                 println(str)
                 violated = crit :: violated
               }

               if(!violated.isEmpty) {
                 violatedConstraint(decodedModel,
                                    node,
                                    candidateModel,
                                    violated) match {
                   case Some(v) => {
                     println("###")
                     value = v
                   }
                       // TODO: Flag conflict for analysis? Widen the interval?
                   case None => done = true
                 }
               } else {
                 done = true
               }
             }
           }
         }
      }
    }

    // TODO: Is this actually a partial model we are completing
    verbose("Completing the model")
    AST.postVisit(ast,
                  candidateModel,
                  decodedModel,
                  copyFromDecodedModelIfNotSet)
    candidateModel
  }


  // TODO: (Aleks) Better name
  // TODO (ptr): What does this do?
  /** ??????? */
  def violatedConstraint(decodedModel : Model,
                         node : AST,
                         candidateModel : Model,
                         violated : List[AST]) = {
    val eps = uppsat.ast.Leaf(
      FloatingPointTheory.getULP(
        decodedModel(node).symbol.asInstanceOf[FloatingPointLiteral]))
    val lessThan = node <= (decodedModel(node) + eps)
    val greaterThan = node >= (decodedModel(node) - eps)
    val newConjuncts = lessThan :: greaterThan :: violated
    val combinedConstraint = AST(NaryConjunction(newConjuncts.length),
                                 List(),
                                 newConjuncts)

    //    TODO: Eclipse says that v != unknown will *almost* never happen.
    //
    //    val vars = ast.iterator.toList.filter(_.isVariable)
    //
    //   val assertions : List[(ConcreteFunctionSymbol, AST)] =
    //      for (v <- vars if( v != unknown &&
    // candidateModel.contains(v))) yield {
    //          (v.symbol, candidateModel(v))
    //      }

    val assertions = List()
    ModelEvaluator.evalAST(combinedConstraint,
                           node.symbol, assertions, inputTheory)
  }

  // TODO: (Aleks) Should this only update the candidateModel if ast has
  // children?
  // TODO (ptr): What does this do?
  /** ??????? */
  def evaluateNode(decodedModel  : Model,
                   candidateModel : Model,
                   ast : AST) : Model = {
    ast match {
      case AST(symbol, label, List()) => ()
      case AST(symbol, label, children) if !candidateModel.contains(ast) => {
        val newChildren = children.map{
          getCurrentValue(_, decodedModel, candidateModel)
        }
        val newAST = AST(symbol, label, newChildren.toList)
        val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
        candidateModel.set(ast, newValue)
      }
    }
    candidateModel
  }


  // TODO (ptr): What does this do?
  /** ??????? */
  def getCurrentValue(ast : AST,
                      decodedModel : Model,
                      candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel(ast)
  }


  // TODO (ptr): What does this do?
  /** ??????? */
  def copyFromDecodedModelIfNotSet (decodedModel : Model,
                                    candidateModel : Model,
                                    ast : AST) = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel
  }
}
