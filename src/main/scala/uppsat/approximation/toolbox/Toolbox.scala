package uppsat.approximation.toolbox



import uppsat.approximation._
import scala.collection.mutable.{HashMap, MultiMap}



import uppsat.theory.Theory
import uppsat.ast.AST
import scala.collection.mutable.Set
import uppsat.ast.ConcreteSort
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelEvaluator.Model
import uppsat.ModelEvaluator
import uppsat.Timer
import uppsat.globalOptions._
import uppsat.theory.FloatingPointTheory
import uppsat.theory.BooleanTheory._
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.IntegerTheory.IntEquality
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.ast.IndexedFunctionSymbol


object Toolbox {
  // A critical atom is a Boolean node which has at least one non-Boolean child and all ancestors are Boolean nodes
  
  /**
   * Returns all critical atoms in ast using decoded model to decide which are relevant
   * 
   * If a conjunction has been evaluated to true in decodedModel, then all children are critical atoms
   * since they all must be true for the conjunction to be true. On the other hand, if a disjunction is true
   * only one child need to be evaluted to true and the first such child is picked as a critical atom.
   * 
   * @param decodedModel Model giving values to the nodes in ast.
   * @param ast The ast which critical atoms are extracted from.
   */
  def retrieveCriticalAtoms(decodedModel : Model)(ast : AST) : List[AST] = {
      val value = decodedModel(ast)
      ast match {
        case AST(symbol, label, children) if (symbol.sort == BooleanSort) => {
          val nonBoolChildren = children.filter((x : AST) => x.symbol.sort != BooleanSort)
          if (nonBoolChildren.length > 0) {
            List(ast)
          } else {
            (symbol, value.symbol) match {

              case (_ : NaryConjunction, BoolTrue)
              |    (    BoolConjunction, BoolTrue) =>
                children.map(retrieveCriticalAtoms(decodedModel)).flatten

              case (_ : NaryConjunction, BoolFalse)
              |    (    BoolConjunction, BoolFalse) => {
                val falseConjuncts = children.filter((x : AST) => decodedModel(x).symbol == BoolFalse)
                if (falseConjuncts.length == 0)
                  throw new Exception(" Retrieve Critical Literalas : False conjunction with no false child.")
                // TODO: We must not always take the first false child. Heuristics possible.
                retrieveCriticalAtoms(decodedModel)(falseConjuncts.head)
              }

              case (BoolDisjunction, BoolTrue) =>
                val trueDisjuncts = children.filter((x : AST) => decodedModel(x).symbol == BoolTrue)
                if (trueDisjuncts.length == 0)
                  throw new Exception("Retrieve Critical Literals : True disjunction with no true child")
                // TODO: We need not always take the first false child. Heuristics possible.
                retrieveCriticalAtoms(decodedModel)(trueDisjuncts.head)

              case (BoolDisjunction, BoolFalse) => 
                (for (c <- children) yield retrieveCriticalAtoms(decodedModel)(c)).flatten

              case (BoolImplication, BoolFalse) => 
                (for (c <- children) yield retrieveCriticalAtoms(decodedModel)(c)).flatten

              case (BoolImplication, BoolTrue) => {
                val antecedent = decodedModel(children(0))
                if (antecedent.symbol == BoolTrue)
                  retrieveCriticalAtoms(decodedModel)(children(1)) // _ => True is True 
                else
                  retrieveCriticalAtoms(decodedModel)(children(0)) // F => _ is True
              }

              case (BoolEquality, _) | (BoolNegation, _) =>
                (for (c <- children) yield retrieveCriticalAtoms(decodedModel)(c)).flatten

              case _ => List(ast)
            }
          }
        }
        case _ => List()
      }
    }
  
  
  def booleanComparisonOfModels(ast : AST, decodedModel : Model, failedModel : Model) : List[AST] = {
    def boolCond( accu : List[AST], ast : AST) : Boolean = {
      decodedModel(ast) != failedModel(ast)
    }

    def boolWork( accu : List[AST], ast : AST) : List[AST] = {
      ast :: accu
    }

    AST.boolVisit(ast, List(), boolCond, boolWork).toSet.toList
  }
  
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
      verbose(ast.symbol + " " + ast.label + " " + " <- " + decodedModel(ast).symbol)
      candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel(ast)
  }
  
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
  

  // TODO: This should be elsewhere, implement using an explicit ordering
  
  def sortLessThan(s1 : ConcreteSort, s2 : ConcreteSort) = {
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
  

      import scala.collection.mutable.{Set => MSet}
    import scala.collection.mutable.Set
  
def topologicalSortEqualities(allDependencies : HashMap[AST, Set[(Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol)]]) : List[AST] = {

    val allEqualities : MSet[AST] = MSet()
    allEqualities ++= allDependencies.keySet
    
    val definedSymbols : MSet[ConcreteFunctionSymbol] = MSet()
    
    var independentEqualities =  List() : List[AST]

    while (!allEqualities.isEmpty) {
      val remEqs = allEqualities.toList
      var next = remEqs.head
      
      val implications = allDependencies(next)
      var cnt = (for ((antecedent, _) <- implications) yield { (antecedent diff definedSymbols).size }).min
      
      for ( eq <- remEqs.tail) {
        val imps = allDependencies(eq)
        val curr = (for ((ants, _) <- imps) yield { (ants diff definedSymbols).size }).min      
        if (curr < cnt) {
          next = eq
          cnt = curr
        }
      }
      
      // TODO: if cyclic dependency exists, all the remaining keys need to be removed
      
      val imps = allDependencies(next)
      val asd = imps.dropWhile(x => (x._1 diff definedSymbols).size != cnt)
      val (ants, cons) = imps.dropWhile(x => (x._1 diff definedSymbols).size != cnt).head
      definedSymbols += cons
      definedSymbols ++= ants
      allEqualities.remove(next)
      
      print(">>")
      next.prettyPrint
      
      independentEqualities = next :: independentEqualities
    }
    println("Done")
    independentEqualities.toList.reverse
  }    
 
}