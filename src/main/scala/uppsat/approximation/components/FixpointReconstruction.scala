package uppsat.approximation.components

import uppsat.theory.Theory

import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
import uppsat.ast.Leaf
import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap

import uppsat.Timer
import uppsat.ast.ConcreteSort
import uppsat.precision.PrecisionOrdering
import uppsat.ast._
import uppsat.precision.PrecisionMap.Path

import uppsat.theory.BooleanTheory.BoolTrue
import uppsat.theory.FloatingPointTheory
import uppsat.ModelReconstructor.Model
import uppsat.ModelReconstructor
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory.BooleanSort
import uppsat.theory.BooleanTheory.BoolConjunction
import uppsat.theory.BooleanTheory.BoolFalse
import uppsat.theory.BooleanTheory.BoolDisjunction
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.BooleanTheory.BoolImplication
import uppsat.theory.BooleanTheory.BoolNegation
import uppsat.theory.BooleanTheory.NaryConjunction
import uppsat.globalOptions._
import uppsat.theory.FloatingPointTheory.FloatingPointPredicateSymbol
import uppsat.theory.FloatingPointTheory.FPEqualityFactory
import uppsat.globalOptions
import uppsat.globalOptions._
import uppsat.solver.Z3Solver
import uppsat.theory.BooleanTheory.BooleanConstant
import uppsat.theory.FloatingPointTheory.RoundingModeEquality
import scala.collection.mutable.ArrayStack
import scala.collection.mutable.Leaf
import scala.collection.mutable.Queue
import uppsat.theory.FloatingPointTheory.FPPredicateSymbol
import scala.collection.mutable.ArrayBuffer
import uppsat.theory.FloatingPointTheory.RoundingModeSort
import scala.collection.mutable.HashMap
import scala.collection.mutable.MultiMap
import scala.collection.mutable.Set
import uppsat.theory.FloatingPointTheory.FPFunctionSymbol
import uppsat.theory.FloatingPointTheory.FPSpecialValuesFactory
import uppsat.theory.FloatingPointTheory.FloatingPointLiteral
import uppsat.solver.Z3OnlineSolver


trait FixpointReconstruction extends ModelReconstructor {

class FixpointException(msg : String) extends Exception("FixpointException: " + msg)

  // Precondition : number of undefined arguments it exactly one. 
  // Some we have a value
  // None means unsat
	/** Returns the assignment of one implied variable in ast (w.r.t. to candidateModel)
	 *
	 *  Assuming that ast w.r.t. candidateModel has exactly one undefined variable,
	 *  getImplication isolates this variable and by calling the back-end solver 
	 *  retrieves a value and returns Some(variable, value) for this pair. If no value
	 *  is found None is returned (thus the candidateModel is *not* a model for ast).
	 *
	 *  @param candidateModel Assignments of some values in ast.
	 *  @param ast The AST with exactly one undefined variable.
	 *
	 *  @return An assignment to the undefined variable in ast s.t. it is compatible with candidateModel.  
 	 *
 	 */
  def getImplication(candidateModel : Model, ast : AST) : Option[(AST, AST)] = {
    val vars = ast.toList.filter(_.isVariable)
    val unknown = vars.filterNot(candidateModel.contains(_)).map(x => (x.symbol, x)).toMap

    unknown.toList match {
      case List((unknownSymbol, unknownAST)) => {
        verbose("Implication of  " +  unknownSymbol + "\n\t" + ast.simpleString())
        val assertions = 
          for ( v <- vars if(candidateModel.contains(v))) yield 
            (v.symbol, candidateModel(v))

        ModelReconstructor.evalAST(ast, unknownSymbol, assertions, inputTheory) match {
          case Some(res) => Some ((unknownAST, res)) 
          case None => None
        }
      }
      case _ => throw new FixpointException("getImplication assumes at most one unknown" + unknown.mkString(", ")) 
    }
  }


  /** The number of variables in ast that are not defined in candidateModel
   *
   *  @param candidateModel Model (possibly) containing variable definitions
   *  @param ast AST (possibly) containing variables
   */
  def numUndefValues(candidateModel : Model, ast : AST) =
    ast.toList.filter((x:AST) => x.isVariable && !candidateModel.contains(x)).map(_.symbol).distinct.length


  def initializeCandidateModel(atoms : List[AST], decodedModel : Model, candidateModel : Model) = {
    // Assert the same literals as in the original model
    for (a <- atoms) {
      if (a.symbol.sort != BooleanSort)
        throw new FixpointException("Non-boolean critical literal" + a)

      if (!candidateModel.contains(a)) 
        candidateModel.set(a, decodedModel(a))
      else if (candidateModel(a) != decodedModel(a))
        throw new Exception("Inconsistent values during model initialization")
    }
  }

  def chooseVar(atoms : List[AST], undefVars : List[AST]) : AST = {
    // TODO: Add heuristic
    undefVars.head
  }

  /** True if ast is a definition
   *  
   *  An ast is a definition if it is an equation where one (or both) sides is a variable.
   *  
   *  @param ast True if ast is a definition
   * 
   */
  // TODO: make meta equality  

  def isDefinition(ast : AST) : Boolean = {
    ast.symbol match {
      case pred : FloatingPointPredicateSymbol 
        if (pred.getFactory == FPEqualityFactory)  => ast.children(0).isVariable || ast.children(1).isVariable
      case BoolEquality
      |    RoundingModeEquality =>
        ast.children(0).isVariable || ast.children(1).isVariable
      case _ => false
    }
  }

  // TODO: make legible
  def isAtom(ast : AST) : Boolean = { 
     ast.symbol.sort == BooleanSort && (ast.isVariable || !ast.children.map(_.symbol.sort).filterNot(_ == BooleanSort).isEmpty)
  }

  // TODO: refactor
  def getBoolDefinitions(ast : AST, polarity : Boolean) : Option[(AST,AST)] = {
    (ast.symbol, polarity) match {
      case (BoolEquality, true) | (RoundingModeEquality, true) | (FPEqualityFactory(_), true) => { 
        (if (ast.children(0).isVariable) Some((ast.children(0), ast)) else  None) orElse
        (if (ast.children(1).isVariable) Some((ast.children(1), ast)) else  None)
      }
      case _ => None
    }
  }

  def topLvlConjuncts(ast : AST) : Iterator[AST]= {
    ast.symbol match {
      case BoolConjunction | _ : NaryConjunction =>
        for ( c <-  ast.children.iterator;
              d <- topLvlConjuncts(c)) yield d
      //case (BoolNegation) => topLvlConjuncts(ast.children(0), !isPositive)
      //case (BoolImplication) => throw new Exception("NYI Implication")
      case _ => Iterator(ast)
    }
  }

  // TODO: This should be elsewhere, implement using an explicit ordering
  import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
  def sortLessThan(s1 : Sort, s2 : Sort) = {
    (s1, s2) match {
      case (BooleanSort, _) => false
      case (_, BooleanSort) => true
      case (RoundingModeSort, _) => false
      case (_, RoundingModeSort) => true
      case (FPSort(eb1, sb1), FPSort(eb2, sb2)) => eb1 + sb1 < eb2 + sb2
      case (FPSort(_, _), _) => false
      case (_, FPSort(_, _)) => true
    }
  }

  // TODO: This should be implicit in AST - this might require a meta-variable notion
  def varToNode(variable : ConcreteFunctionSymbol) : AST = {
    AST(variable, List(), List())
  }

  /** Returns all critical atoms in ast)
   *
   *  TODO (Aleks): What is the difference between this and retrieveCriticalAtoms?
   */
  def extractCriticalAtoms(ast : AST, decodedModel : Model) = {

    val (definitionAtoms, conjuncts) = topLvlConjuncts(ast).toList.partition(isDefinition(_))
    var definitions = for ( a <- definitionAtoms; b <- getBoolDefinitions(a, true)) yield b
    val critical = new ArrayBuffer[AST]

    var todo = new Queue[AST]
    todo ++=  conjuncts
    while (!todo.isEmpty) {

      for (c <- todo) {
        critical ++= ModelReconstruction.retrieveCriticalAtoms(decodedModel)(c)
      }
      todo.clear()

      val vars = (for (c <- critical.iterator;
                       v <- c.iterator.filter(_.isVariable)) yield v.symbol).toSet

      //verbose("Vars(" + vars.size + "):\n\t" + vars.mkString(", "))
      val (toBeAdded, toKeep) = definitions.partition((p) => vars.contains(p._1.symbol))
      todo ++= toBeAdded.map(_._2)
      definitions = toKeep
    }
    (definitions, critical, conjuncts) // TODO: Inspect the correct returns
  }

  /** Returns a topological sorting of the dependencies
   *
   *  Returns a list of corresponding to a topological sorting of the dependency graph implied by allDependencies.
   *  Uses the function sortLessThan as a sorting of sorts to choose which to pick first. 
   *
   * @param allDependencies Dependency edges in the dependency graph.
   *
   * @return A topological sort of the nodes in allDependencies 
   */

  //TODO: Remove the Boolean filter from this function. It should be generic.
  def topologicalSort(allDependencies : HashMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]]) : List[ConcreteFunctionSymbol] = {
    var dependencies = new HashMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]] with MultiMap[ConcreteFunctionSymbol, ConcreteFunctionSymbol]
    for ((k, vs) <- allDependencies;
        v <- vs)
      dependencies.addBinding(k, v)

    val allVars = dependencies.keys.toList
    var independentVars =  allVars.filter(_.sort != BooleanSort).filterNot(dependencies.contains(_)).sortWith((x , y) => !sortLessThan(x.sort,y.sort))

      for ( variable <- independentVars; 
            (k, v) <- dependencies) {
            dependencies.removeBinding(k, variable)
      }
      verbose("Variables :\n\t" + independentVars.mkString("\n\t"))
      verbose("Dependency graph : \n\t" + dependencies.mkString("\n\t"))
      while (!dependencies.isEmpty) {
        var next = dependencies.keys.head
        var cnt = dependencies(next).size
        for ( (key, set) <- dependencies) {
          val curr = set.size
          if (curr < cnt || (curr == cnt && sortLessThan(next.sort, key.sort))){
            next = key
            cnt = curr
          }
        }
        // TODO: if cyclic dependency exists, all the remaining keys need to be removed
        dependencies.remove(next)
        independentVars = next :: independentVars
        for ((k, v) <- dependencies) {
          dependencies.removeBinding(k, next)
        }
      }
      independentVars.toList.reverse
  }

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()

    verbose("Starting fixpoint reconstruction")
    val (definitions, critical, conjuncts) = extractCriticalAtoms(ast, decodedModel)
    verbose("Critical " + critical.mkString("\n\t"))
    verbose("Definitons : " + definitions.mkString("\n"))

    //TODO: Remove duplicate definitions
    //TODO:  Cycle-breaking

    val varsToCritical = new HashMap[ConcreteFunctionSymbol, Set[AST]] with MultiMap[ConcreteFunctionSymbol, AST]
    (for (c <- critical.iterator;
          v <- c.iterator.filter(_.isVariable)) 
          yield (v.symbol, c)).foldLeft(varsToCritical){(acc, pair) => acc.addBinding(pair._1, pair._2)}

    //Fix-point computation
    var done = false
    var changed = false
    var iteration = 0

    val allVars = varsToCritical.keys.toList.sortWith((x,y) => varsToCritical(x).size < varsToCritical(y).size)// sortComparison(x.sort, y.sort))

    // Boolean variables can just be copied over
    for (v <- allVars if v.theory == BooleanTheory)
      copyFromDecodedModelIfNotSet(decodedModel, candidateModel, varToNode(v))

    var varDependency = new HashMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]] with MultiMap[ConcreteFunctionSymbol, ConcreteFunctionSymbol]

    for ( c <- critical.toList if isDefinition(c)) {
      val lhs = c.children(0)
      if (lhs.isVariable && lhs.symbol.theory != BooleanTheory) {
        for ( v <- c.children(1).iterator.filter(_.isVariable))
          varDependency.addBinding(lhs.symbol, v.symbol)
      }
      val rhs = c.children(0)
      if (rhs.isVariable && rhs.symbol.theory != BooleanTheory) {
        for ( v <- c.children(0).iterator.filter(_.isVariable))
          varDependency.addBinding(rhs.symbol, v.symbol)
      }
    }

    val independentVars = topologicalSort(varDependency)

    // TODO: This is theory specific...
    // First migrate special values
    verbose("Migrating special values")

    for (v <- independentVars if v.sort.isInstanceOf[FPSort]) {
      decodedModel(varToNode(v)).symbol.asInstanceOf[IndexedFunctionSymbol].getFactory match { 
        case FPSpecialValuesFactory(_) => verbose("Migrating special value " + decodedModel(varToNode(v)))
                                          candidateModel.set(varToNode(v), decodedModel(varToNode(v)))
        case _ => ()//verbose("Ignoring: " + decodedModel(varToNode(v)).symbol)
      }
    }

    val vars = independentVars.filterNot(candidateModel.variableValuation.contains(_))
    verbose("Sorted variables :\n\t" + vars.mkString("\n\t"))
//    val (nonLhs, lhs) = nonBoolVars.partition(occursOnLhs.contains(_))
//    val vars = nonLhs ++ lhs
    while (! done) {
      iteration += 1
      verbose("=============================\nPatching iteration " + iteration)

      val implications =
        critical.filter { x => x.children.length > 0 && //TODO:  reocnsider the first condition
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
              if (crit.symbol.sort == BooleanSort && candidateModel(crit) != decodedModel(crit)) {
                println("Reconstruction fails for : \n " + node.symbol + "->" + value +
                        "\n Implied by : " + i.simpleString() + 
                        "\n on literal \n" + crit.simpleString() +
                        "\nDecodedModel ===================== " + decodedModel(crit) + "\n\t" +
                        decodedModel.variableAssignments(crit).mkString("\n\t") +
                        "\nCandidateModel ===================== "  + candidateModel(crit)  + "\n\t" +
                        candidateModel.variableAssignments(crit).mkString("\n\t")
                        )
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
         val undefVars = vars.filterNot(candidateModel.containsVariable(_)).toList
         if (undefVars.isEmpty) {
           verbose("No undefined variables ...\n Done supporting critical atoms.")

           // TODO: (Aleks) Do we actually care if the decoded model has extra values?
           for ( (variable, value) <- decodedModel.variableValuation 
                 if (!candidateModel.contains(varToNode(variable)))) {
             //  println("candidate")
             //  println(candidateModel)
             //  println("decoded")
             //  println(decodedModel)
             //  ast.prettyPrint
             //  throw new Exception ("Decoded model contains extra assignments: " + variable)
           }
             //candidateModel.set(varToNode(variable), value)

           //TODO: This should not ever be true
           // val unevaluatedAtoms = critical.filter (!candidateModel.contains(_))
           // for (a <- unevaluatedAtoms) {
           //   AST.postVisit(a, candidateModel, decodedModel, evaluateNode)
           // }
           done = true
         } else {
           val chosen = undefVars.head // TODO: Call the method 
           val node = varToNode(chosen)
           verbose("Copying from decoded model " + chosen + " -> " + decodedModel(node).getSMT())

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
                // We will set the values only of the literals that 
                // have not been evaluated yet and have no unknowns
                // Consider cascading expressions, do we need to watch all of them
                //evaluateNode(decodedModel, candidateModel, crit)

                //ModelReconstructor.onlineSolver.get.asInstanceOf[Z3OnlineSolver].silent = false
                AST.postVisit(crit, candidateModel, candidateModel, evaluateNode)
                //ModelReconstructor.onlineSolver.get.asInstanceOf[Z3OnlineSolver].silent = true

                if (crit.symbol.sort == BooleanSort && candidateModel(crit) != decodedModel(crit)) {
                  println("Migration violates : \n " + node.symbol + "->" + decodedModel(node) +
                          "\n on literal \n" + crit.simpleString() +
                          "\nDecodedModel\n ===================== " + decodedModel(crit) + "\n\t"
                          + decodedModel.variableAssignments(crit).mkString("\n\t") +
                          "\nCandidateModel\n ===================== "  + candidateModel(crit)  + "\n\t"
                          + candidateModel.variableAssignments(crit).mkString("\n\t")
                          )
                  violated = crit :: violated
                }

                if(!violated.isEmpty) {
                  violatedConstraint(decodedModel, node, candidateModel, violated) match {
                    case Some(v) => println("###")
                        value = v
                    case None => done = true //TODO: Flag conflict for analysis? Widen the interval?
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
    AST.postVisit(ast, candidateModel, decodedModel, copyFromDecodedModelIfNotSet)
    candidateModel
  }

  // TODO: (Aleks) Better name
  def violatedConstraint(decodedModel : Model, node : AST, candidateModel : Model, violated : List[AST]) = {
    val eps = uppsat.ast.Leaf(FloatingPointTheory.getULP(decodedModel(node).symbol.asInstanceOf[FloatingPointLiteral]))
    val lessThan = node <= (decodedModel(node) + eps) 
    val greaterThan = node >= (decodedModel(node) - eps)
    val newConjuncts = lessThan :: greaterThan :: violated
    val combinedConstraint = AST(NaryConjunction(newConjuncts.length), List(), newConjuncts)                  

    //    TODO: (Aleks) Eclipse says that v != unknown will *almost* never happen.
    // 
    //    val vars = ast.iterator.toList.filter(_.isVariable)
    //    
    //   val assertions : List[(ConcreteFunctionSymbol, AST)] = 
    //      for ( v <- vars if( v != unknown && candidateModel.contains(v))) yield {        
    //          (v.symbol, candidateModel(v))
    //      }
        
    val assertions = List()
    ModelReconstructor.evalAST(combinedConstraint, node.symbol, assertions, inputTheory)
  }
    
   
  // TODO: (Aleks) Should this only update the candidateModel if ast has children?
  def evaluateNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    ast match {
      case AST(symbol, label, List()) => ()
      case AST(symbol, label, children) if !candidateModel.contains(ast) => {
        val newChildren = children.map(getCurrentValue(_, decodedModel, candidateModel))
        val newAST = AST(symbol, label, newChildren.toList)
        val newValue = ModelReconstructor.evalAST(newAST, inputTheory)
        candidateModel.set(ast, newValue)
      }
    }
    candidateModel  
  }
    
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    } 
    candidateModel(ast)
  }
  
  def copyFromDecodedModelIfNotSet (decodedModel : Model, candidateModel : Model, ast : AST) = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel
  }
}
