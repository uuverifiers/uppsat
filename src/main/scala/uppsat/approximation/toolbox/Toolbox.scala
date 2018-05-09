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
  

      import scala.collection.mutable.{Set => MSet, ListBuffer}
      import scala.collection.immutable.Set
        type Implication = (scala.collection.immutable.Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol)

  
//def topologicalSortEqualities(allDependencies : HashMap[AST, Set[(Set[ConcreteFunctionSymbol], ConcreteFunctionSymbol)]]) : List[AST] = {
  def topologicalSortEqualities(allEquations : List[AST]) : List[AST] = {

    val allVariables = allEquations.map(_.iterator.filter(_.isVariable).toSet).flatten.map(_.symbol).toSet        

    // Let's begin by creating a partial order over variables
    
   
    for (eq <- allEquations)
      eq.prettyPrint
      
      
    val simpleEqualities = MSet() : MSet[AST]
    val definingEqualities = MSet() : MSet[AST]
    val complexEqualities = MSet() : MSet[AST]
    
    for (eq <- allEquations) {
      (eq.children(0).isVariable, eq.children(1).isVariable) match {
        case (true, true) => simpleEqualities += eq
        case (true, false) | (false, true) => definingEqualities += eq
        case (false, false) => complexEqualities += eq
      }
    }

    // Simple equalities x = y yields a dependence x -> y as well as y -> x
    // Defining equlaities x = exp yield a dependences x -> vars(exp)
    // Complex equlities are just ignored for now
    var undefVars = MSet() ++ allVariables
    var defVars = MSet() : MSet[ConcreteFunctionSymbol]
    var varOrder = ListBuffer() : ListBuffer[ConcreteFunctionSymbol]
    
    val implications = new HashMap[ConcreteFunctionSymbol, MSet[Set[ConcreteFunctionSymbol]]] with MultiMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]]
    for (seq <- simpleEqualities) {
      val lhs = seq.children(0).symbol
      val rhs = seq.children(1).symbol
      implications.addBinding(lhs, Set(rhs))
      implications.addBinding(rhs, Set(lhs))
    }
    
    for (deq <- definingEqualities) {
      val definedVar = 
        if (deq.children(0).isVariable) 
          deq.children(0).symbol
        else
          deq.children(1).symbol
          
      val definingVars =
        if (deq.children(0).isVariable)
          deq.children(1).iterator.filter(_.isVariable).map(_.symbol).toSet
        else
          deq.children(0).iterator.filter(_.isVariable).map(_.symbol).toSet

      implications.addBinding(definedVar, definingVars)
    }
   
    
    def mostConstrainedVar(vars : List[ConcreteFunctionSymbol]) : ConcreteFunctionSymbol = {
      val antCount = new HashMap[ConcreteFunctionSymbol, Int]
      
      for ((_, ants) <- implications; ant <- ants; a <- ant) {
        antCount += a -> ((antCount.getOrElse(a, 0)) + 1) 
      }
           
      var best = vars.head
      // I thought this could never be undefined but apparently it can
      var count = antCount.getOrElse(vars.head, 0)
      for (v <- vars.tail) {
        if (antCount.getOrElse(v, 0) > count) {
          best = v
          count = antCount(v)
        }
      }
      best
    }
    
    def findDefinableVar(vars : List[ConcreteFunctionSymbol]) : Option[ConcreteFunctionSymbol] = {
      vars match {
        case Nil => None
        case h :: tail => {
          // Check if h is good candidate
          if (implications(h).exists(x => (x diff defVars).isEmpty)) {
            implications.remove(h)
            Some(h)
          } else {
            findDefinableVar(tail)
          }
        }
      }
    }
    
    def defineVar(v : ConcreteFunctionSymbol) = {
      defVars += v
      varOrder += v
      undefVars -= v
    }
   
    
//    println("allEquations:")
//    for (eq <- allEquations)
//      eq.prettyPrint(".")
//    println("IMPLICATIONS:")
//    println(implications.mkString("\n"))


    for (v <- allVariables) {
      // If nothing implies this variable, just define it right away
      if (!(implications contains v) || (implications(v).exists(_.isEmpty)))
        defineVar(v)
    }
    
//    println("PreDefined: " + varOrder.mkString(", "))
    
    while (!undefVars.isEmpty) {
      val v = 
        findDefinableVar(undefVars.toList) match {
          case Some(v) => v
          case None => mostConstrainedVar(undefVars.toList)
      }
//      println("Defining: " + v)
      defineVar(v)
    }
    
    val eqOrder = ListBuffer() : ListBuffer[AST]
    var remEquations = MSet() ++ allEquations
    println("varOrder: " + varOrder.mkString(","))
    
    def isDefined(eq : AST) = {
      val vars = eq.iterator.filter(_.isVariable).map(_.symbol).toSet
      (vars intersect varOrder.toSet).isEmpty 
    }
    
    while (!remEquations.isEmpty) {
      // Remove first element
      val v = varOrder.head
      varOrder = varOrder.tail
      val rEqs = remEquations.toList
      for (req <- rEqs; if isDefined(req)) {
        eqOrder += req
        remEquations -= req
      }
      //Add all remaining equalities which are now defined
    }
    
    println("EQOrder: ")
    for (eq <- eqOrder)
		  eq.prettyPrint("..")
		  
		eqOrder.toList
  }     
}



//def topologicalSortEqualities(allEquations : List[AST]) : List[AST] = {
//
//    for (eq <- allEquations)
//      eq.prettyPrint
//      
//    val simpleEqualities = MSet() : MSet[AST]
//    val definingEqualities = MSet() : MSet[AST]
//    val complexEqualities = MSet() : MSet[AST]
//    
//    for (eq <- allEquations) {
//      (eq.children(0).isVariable, eq.children(1).isVariable) match {
//        case (true, true) => simpleEqualities += eq
//        case (true, false) | (false, true) => definingEqualities += eq
//        case (false, false) => complexEqualities += eq
//      }
//    }
//    
//    var badVariables = MSet() : MSet[ConcreteFunctionSymbol]
//    
//    // Maps function symbols to all simple equations containing it as well as the other side of the equation
//    val simpleMap = new HashMap[ConcreteFunctionSymbol, MSet[(AST, ConcreteFunctionSymbol)]] with MultiMap[ConcreteFunctionSymbol, (AST, ConcreteFunctionSymbol)]
//    for (eq <- simpleEqualities) yield {
//      val (v1, v2) = (eq.children(0).symbol, eq.children(1).symbol)
//      simpleMap.addBinding(v1, (eq, v2))
//      simpleMap.addBinding(v2, (eq, v1))
//      // Try changing this
//      badVariables += v1
//      badVariables += v2
//    }
//    
//    // Contains tuples Set[ConcreteFunctionSymbol] => AST
//    val complexList = 
//      for (eq <- complexEqualities.toList) yield {
//        (eq.iterator.filter(_.isVariable).map(_.symbol).toSet, eq)
//      }
//    
//    val definingMap = new HashMap[AST, Implication]
//    
//    for ( eq <- allEquations.toList) {
//      val definedVar = 
//        if (eq.children(0).isVariable) 
//          eq.children(0).symbol
//        else
//          eq.children(1).symbol
//          
//      val definingVars =
//        if (eq.children(0).isVariable)
//          eq.children(1).iterator.filter(_.isVariable).map(_.symbol).toSet
//        else
//          eq.children(0).iterator.filter(_.isVariable).map(_.symbol).toSet
//
//      badVariables += definedVar
//      definingMap += eq -> (definingVars, definedVar)
//    }      
//           
//    
//    //val undefinedVariables : MSet[ConcreteFunctionSymbol] = MSet() ++ allEquations.map(_.iterator.filter(_.isVariable).map(_.symbol)).toSet.flatten
//    val allVariables = allEquations.map(_.iterator.filter(_.isVariable).map(_.symbol)).toSet.flatten
//
//    val definedVariables : MSet[ConcreteFunctionSymbol] = (MSet() ++ allVariables) diff badVariables
//    
//    println("allvariables: " + allVariables)
//    println("bad variables: " + badVariables)
//    println("Defined variables: " + definedVariables)
//      
//    var sortedEqualities =  List() : List[AST]
//
//    // So in each iteration we want to find a variable which either:
//    // (i)  Is defined by any equation in definingMap
//    // (ii) ... lets find more cases
//    
//    def defineVariable(v : ConcreteFunctionSymbol) : Unit = {
////      println("defineVariable(" + v + ")")
//      definedVariables += v      
//      if (!(definedVariables contains v)) {
//        // Go through simple map
//        if (simpleMap contains v) {
//          val simpleEqs = simpleMap.remove(v).get
//          for ((seq, svar) <- simpleEqs) {
//            sortedEqualities = seq :: sortedEqualities
//            simpleEqualities -= seq
//            defineVariable(svar)
//          }                 
//        }
//      }
//    }
//    
//    while (!definingEqualities.isEmpty) {
//      
//     
//      def antCount(v : ConcreteFunctionSymbol) : Int = {
//        (for (deq <- definingEqualities) yield {
//          val (defVars, defVar) = definingMap(deq)
//          if (defVars contains v) 1 else 0
//        }).sum
//      }
//      
//      def findDefiningEquality(remEqs : List[AST]) : AST = {
//        remEqs match {
//          case Nil => {
////            println("No suitable equality found, picking a variable instead")
//            // Define a variable instead
//            val undefVars = allVariables diff definedVariables
//            var best = undefVars.head
//            var value = antCount(best) 
//            for (v <-undefVars.tail) {
//              if (antCount(v) < value) {
//                best = v
//                value = antCount(v)
//              }
//            }
//            defineVariable(best)
//            findDefiningEquality(definingEqualities.toList)
//          }
//          case eq :: rest => {
//            val (dVars, _) = definingMap(eq)
//            if ((dVars diff definedVariables).isEmpty)
//              eq
//            else
//              findDefiningEquality(rest)
//          }
//        }
//      }
//      
//      val next = findDefiningEquality(definingEqualities.toList)
//      definingEqualities -= next
//      sortedEqualities = next :: sortedEqualities
//      val (defVars, defVar) = definingMap(next)
//      // defVar is now defined
//      defineVariable(defVar)
//      
//    }
//    
//    // We are probably going to process simple equalities twice now
//    for (seq <- simpleEqualities) {
//      sortedEqualities = seq :: sortedEqualities
//    }
//    
//    for (ceq <- complexEqualities) {
//      sortedEqualities = ceq :: sortedEqualities
//    }
//    
//    println("Don't forget to add complex and remaingin simple equations")
//    println("Done")
//    sortedEqualities.toList.reverse
//  }    
// 
//}
//    val symDependency = new HashMap[ConcreteFunctionSymbol, Set[Set[ConcreteFunctionSymbol]]] with MultiMap[ConcreteFunctionSymbol, Set[ConcreteFunctionSymbol]]
//
//    for ((_, imps) <- allDependencies) {
//        for ((ant, con) <- imps) {
//          symDependency.addBinding(con, ant)
//        }
//    }
//    
//    for (v <- allVariables) {
//      println("Checking:" + v)
//      val deps = symDependency(v)
//      println("\t" + deps)
//      if (deps.isEmpty || deps.head.isEmpty) {
//        definedSymbols += v
//        println("Added: " + v)
//      } else {
//        println("Set nonempty: " + deps.mkString(","))
//      }
//      } else if (deps.size == 1 && deps.head.size == 1)) {
//    }
//    
//    println("All vars:")
//    println(allVariables)
//    println("Pre-defined symbols:")
//    println(definedSymbols.mkString(", "))
