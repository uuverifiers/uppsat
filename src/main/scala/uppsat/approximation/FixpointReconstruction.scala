package uppsat.approximation

import uppsat.theory.Theory

import uppsat.precision.PrecisionOrdering
import uppsat.ast.AST
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


trait FixpointReconstruction extends ApproximationCore {
  
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
                (for (c <- children) yield retrieveCriticalAtoms(decodedModel)(c)).flatten
                
              case (_ : NaryConjunction, BoolFalse)
              |    (    BoolConjunction, BoolFalse) => {
                val falseConjuncts = children.filter((x : AST) => decodedModel(x).symbol == BoolFalse)
                if (falseConjuncts.length == 0)
                  throw new Exception("False conjunction has no false children")
                retrieveCriticalAtoms(decodedModel)(falseConjuncts.head)
              }
              
              case (BoolDisjunction, BoolTrue) =>
                val trueDisjuncts = children.filter((x : AST) => decodedModel(x).symbol == BoolTrue)
                if (trueDisjuncts.length == 0)
                  throw new Exception("True disjunction has no true children")
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
  
  
  
  // Precondition : number of undefined arguments it at most one. 
  def getImplication(candidateModel : Model, ast : AST) : Option[(AST, AST)] = {
    val vars = ast.iterator.toList.filter(_.isVariable)
    
    val assertions : List[(ConcreteFunctionSymbol, AST)] = 
      for ( v <- vars if(candidateModel.contains(v))) yield {        
          (v.symbol, candidateModel(v))
      }
    
    val unknown = vars.filterNot(candidateModel.contains(_)).map(x => (x.symbol, x)).toMap
    
    
    if (unknown.size > 1) 
      throw new Exception("getImplication assumes at most one unknown" + unknown.mkString(", "))
    
    
    if (unknown.size == 1) {
      println("Implication of  " +  unknown.keys.head + "\n\t" + ast.simpleString())
      val result = ModelReconstructor.evalAST(ast, unknown.keys.head, assertions, inputTheory)
      result match {
        case Some(res) => println(">> " + res.symbol) 
                          Some ((unknown.values.head, res))
        case None => None
      }
    } else
      None
    
  }
  
  
  //undefinedVariables.Length
  def numUndefValues(candidateModel : Model, ast : AST) : Int = {
    undefinedVariables(candidateModel, ast).length    
  }
  
  def undefinedVariables(candidateModel : Model, ast : AST) : List[ConcreteFunctionSymbol] = {
    ast.iterator.toList.filter((x:AST) => x.isVariable && !candidateModel.contains(x)).map(_.symbol).distinct
  }
  
  def initializeCandidateModel(atoms : List[AST], decodedModel : Model, candidateModel : Model) = {
    // Assert the same literals as in the original model
    for (a <- atoms) {
      if (a.symbol.sort != BooleanSort)
        throw new Exception("Non-boolean critical literal" + a)
      
      if (!candidateModel.contains(a)) 
        candidateModel.set(a, decodedModel(a))
      else if (candidateModel(a) != decodedModel(a))
        throw new Exception("Inconsistent values during model initialization")
    }
  }
  
  def chooseVar(atoms : List[AST], undefVars : List[AST]) : AST = {
    undefVars.head
  }
  
  def isDefinition(ast : AST) : Boolean = {
    ast.symbol match {
      case pred : FloatingPointPredicateSymbol 
        if (pred.getFactory == FPEqualityFactory)  => {
            if (ast.children(0).isVariable || ast.children(1).isVariable)
              true
            else
              false
        }
      case BoolEquality
      |    RoundingModeEquality =>
        if (ast.children(0).isVariable || ast.children(1).isVariable)
              true
            else
              false
      case _ => false
    }
  }
  
  def getDefinitions(ast : AST, polarity : Boolean) = {
    (ast.symbol, polarity) match {
      case (pred : FloatingPointPredicateSymbol, true) 
        if (pred.getFactory == FPEqualityFactory)  =>
            val left = if (ast.children(0).isVariable)   Some((ast.children(0), ast.children(1)))
                       else None
                          
            val right = if (ast.children(1).isVariable)  Some((ast.children(1), ast.children(2)))
                        else  None
          
            List(left, right)
      case (BoolEquality, true)
      |    (RoundingModeEquality, true) =>
        val left = if (ast.children(0).isVariable)   Some((ast.children(0), ast.children(1)))
                       else None
                          
        val right = if (ast.children(1).isVariable)  Some((ast.children(1), ast.children(2)))
                    else  None
      
        List(left, right)
      case _ => List()
    }
  }
  
  def isAtom(ast : AST) : Boolean = { 
     ast.symbol.sort == BooleanSort && (ast.isVariable || !ast.children.map(_.symbol.sort).filterNot(_ == BooleanSort).isEmpty)
  }
  
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
  
  def criticalAtoms(formula : AST, decodedModel : Model, equalities : List[AST], definitions : List[(AST, AST)]) = {
     var todo = new Queue[AST]()
     todo.enqueue(formula)
     
     var criticalAtoms : List[AST] = List()
     
     while(!todo.isEmpty) {
       val node = todo.dequeue()
       
       if (isAtom(node)) {
           println("Critical " + node.simpleString())
           criticalAtoms = node :: criticalAtoms
       }
       
       if(node.isVariable) {
         val  defs = definitions.filter(_._1 == node) 
         for ((_,d) <- defs) { //There should be only 1 most often
           println("Def " + d.simpleString())
           for (a <- retrieveCriticalAtoms(decodedModel)(d) if !equalities.contains(a)){
             println("Enq. " + a.simpleString())
             todo.enqueue(a)        
           }
         }
       } else {
         for (a <- retrieveCriticalAtoms(decodedModel)(node) if !equalities.contains(a)) {
             println("Enq. " + a.simpleString())
             todo.enqueue(a)
         }
       }
     }
     
    criticalAtoms
  }
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
  
  
  def varToNode(variable : ConcreteFunctionSymbol) : AST = {
    AST(variable, List(), List())
  }
  
  def extractCriticalAtoms( ast : AST, decodedModel : Model) = {
    
    val (definitionAtoms, conjuncts) = topLvlConjuncts(ast).toList.partition(isDefinition(_))
    var definitions = for ( a <- definitionAtoms; b <- getBoolDefinitions(a, true)) yield b
    val critical = new ArrayBuffer[AST]
    
    var todo = new Queue[AST]
    todo ++=  conjuncts
    while (!todo.isEmpty) {
      
      for (c <- todo) {
        critical ++= retrieveCriticalAtoms(decodedModel)(c)
      }
      todo.clear()
      
      val vars = (for (c <- critical.iterator;
                       v <- c.iterator.filter(_.isVariable)) yield v.symbol).toSet
      
      //verbose("Vars(" + vars.size + "):\n\t" + vars.mkString(", "))                       
      val (toBeAdded, toKeep) = definitions.partition((p) => vars.contains(p._1.symbol))
      todo ++= toBeAdded.map(_._2)
      definitions = toKeep
    }
    (definitions, critical, conjuncts)
  }
  
  def fixPointBasedReconstruction(ast : AST, decodedModel : Model) : Model = {
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
    
    var variables =  allVars.filter(_.sort != BooleanSort).filterNot(varDependency.contains(_)).sortWith((x , y) => !sortLessThan(x.sort,y.sort))
    
    for ( variable <- variables; 
          (k, v) <- varDependency) {
          varDependency.removeBinding(k, variable)
    }
    println("Variables :\n\t" + variables.mkString("\n\t"))
    println("Dependency graph : \n\t" + varDependency.mkString("\n\t"))
    while (!varDependency.isEmpty) {
      var next = varDependency.keys.head
      var cnt = varDependency(next).size
      for ( (key, set) <- varDependency) {
        val curr = set.size
        if (curr < cnt || (curr == cnt && sortLessThan(next.sort, key.sort))){
          next = key
          cnt = curr
        }
      }
      // Cyclic dependency exists, all the remaining keys need to be removed
      varDependency.remove(next)
      variables = next :: variables
      for ((k, v) <- varDependency) {
        varDependency.removeBinding(k, next)
      }
    }
    
    
                        
    // First migrate special values
    for (v <- variables if v.sort == FPSort && 
        decodedModel(varToNode(v)).symbol.asInstanceOf[IndexedFunctionSymbol].getFactory.isInstanceOf[FPSpecialValuesFactory]) 
      candidateModel.set(varToNode(v), decodedModel(varToNode(v)))
    
    
    val vars = variables.filterNot(candidateModel.variableValuation.contains(_))//.reverse
    println("Sorted variables :\n\t" + vars.mkString("\n\t"))
//    val (nonLhs, lhs) = nonBoolVars.partition(occursOnLhs.contains(_))  
//    val vars = nonLhs ++ lhs
    while (! done) {
      iteration += 1
      verbose("=============================\nPatching iteration " + iteration)
      
      
      val implications = critical.filter { x => x.children.length > 0 && isDefinition(x) && numUndefValues(candidateModel, x) == 1 }.sortBy(_.iterator.size)
      verbose("Implications(" + implications.length + "):")
      verbose(implications.map(_.simpleString()).mkString("\n\t"))
      verbose("**************************************************")
      changed = false
      
      
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
              AST.postVisit(crit, candidateModel, candidateModel, evaluateNode)
              if (crit.symbol.sort == BooleanSort && candidateModel(crit) != decodedModel(crit)) {
                println("Reconstruction fails for : \n " + node.symbol + "->" + value +
                        "\n Implied by : " + i.simpleString() + 
                        "\n on literal \n" + crit.simpleString() +
                        "\nDecodedModel\n ===================== " + decodedModel(crit) + "\n\t"
                        + decodedModel.getAssignmentsFor(crit).mkString("\n\t") +
                        "\nCandidateModel\n ===================== "  + candidateModel(crit)  + "\n\t"
                        + candidateModel.getAssignmentsFor(crit).mkString("\n\t")
                        )                
              }              
            }            
            changed = true
          }
          case None => ()
        }
      }
      
      
      // order 
      if (!changed) {
         verbose("No implications ... ")
         val undefVars = vars.filterNot(candidateModel.containsVariable(_)).toList
         if (undefVars.isEmpty) {
           verbose("No undefined variables ...\n Done satisfying critical atoms.")
           
           for ( (variable, value) <- decodedModel.variableValuation if (!candidateModel.contains(varToNode(variable))))
             candidateModel.set(varToNode(variable), value)
           
           val unevaluatedAtoms = critical.filter { x => numUndefValues(candidateModel, x) > 0 }
           for (a <- unevaluatedAtoms) {
             AST.postVisit(a, candidateModel, decodedModel, evaluateNode)
           }
           done = true
         } else {
           val chosen = undefVars.head
           val node = varToNode(chosen)
           println("Copying from decoded model " + chosen + " -> " + decodedModel(node).getSMT())
           
           candidateModel.set(node, decodedModel(node))
           
           
           //TODO:  Construct one huge mega query to find this value?
           var violated : List[AST] = List()
           for ( crit <-  varsToCritical(node.symbol) 
                if !candidateModel.contains(crit) 
                && numUndefValues(candidateModel, crit) == 0) {
              // We will set the values only of the literals that 
              // have not been evaluated yet and have no unknowns
              // Consider cascading expressions, do we need to watch all of them
              //evaluateNode(decodedModel, candidateModel, crit)
              AST.postVisit(crit, candidateModel, candidateModel, evaluateNode)
              if (crit.symbol.sort == BooleanSort && candidateModel(crit) != decodedModel(crit)) {
                println("Reconstruction fails for : \n " + node.symbol + "->" + decodedModel(node) +
                        "\n on literal \n" + crit.simpleString() +
                        "\nDecodedModel\n ===================== " + decodedModel(crit) + "\n\t"
                        + decodedModel.getAssignmentsFor(crit).mkString("\n\t") +
                        "\nCandidateModel\n ===================== "  + candidateModel(crit)  + "\n\t"
                        + candidateModel.getAssignmentsFor(crit).mkString("\n\t")
                        )                
              }              
              
              if (crit.symbol.sort == BooleanSort && decodedModel(crit) != candidateModel(crit))
                violated = crit :: violated
            }
         }           
      }
    }
    
    verbose("Completing the model")
    AST.postVisit(ast, candidateModel, decodedModel, copyFromDecodedModelIfNotSet)
    candidateModel
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    fixPointBasedReconstruction(ast, decodedModel)
  }
 
  def evaluateNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    
    if (!candidateModel.contains(ast)) {
      if (children.length > 0) {
        val newChildren = for ( c <- children) yield {        
          getCurrentValue(c, decodedModel, candidateModel)
        }
     
        //Evaluation
        verbose(">> " + ast.simpleString())
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