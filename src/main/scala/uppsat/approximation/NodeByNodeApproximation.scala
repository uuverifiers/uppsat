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
import uppsat.theory.FloatingPointTheory.FPEqualityFactory // TODO: isEquality method should be added so that Equality as assignment is not tied to any particular Theory
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

trait NodeByNodeApproximation extends Approximation {  
  def encodeNode(ast : AST, children : List[AST], precision : P) : AST
  def decodeNode( args : (Model, PrecisionMap[P]), decodedModel : Model, ast : AST) : Model
  def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model 
  def cast(ast : AST, target : ConcreteSort  ) : AST // PrecisionOrdering ? 
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]
  def satRefinePrecision( node : AST, pmap : PrecisionMap[P]) : P
  def unsatRefinePrecision( p : P) : P
  
  
  //Parameters for SAT refinement 
  val topK : Int
  val fractionToRefine : Double 
  val precisionIncrement : P
    
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }    
    encodeNode(ast, newChildren, pmap(ast.label))    
  }
  
  def booleanComparisonOfModels(ast : AST, decodedModel : Model, failedModel : Model) : List[AST] = {
      def boolCond( accu : List[AST], ast : AST, path : Path) : Boolean = {
        decodedModel(ast) != failedModel(ast)
      }
      
      def boolWork( accu : List[AST], ast : AST) : List[AST] = {      
        ast :: accu
      }
      
      AST.boolVisit(ast, List(), boolCond, boolWork).toSet.toList
  }
  
  // Relies on decodeNode method being supplied by the user
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
  
  
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
    var unknown : List[AST]= List()
    debug("Original node : ")
    if (DEBUG) 
        ast.prettyPrint("")
        
    val newChildren = for ( a <- ast.children) yield {
      if (candidateModel.contains(a))
        candidateModel(a)
      else
        unknown = a :: unknown
        a
    }
    
    unknown = unknown.distinct
    if (unknown.length > 1) 
      throw new Exception("getImplication assumes at most one unknown" + unknown.mkString(", "))
    
    debug("Implication : " + ast.symbol)
    debug("Children " + newChildren.mkString(", "))
    val substitutedAST = AST(ast.symbol, ast.label, newChildren)
    debug("new tree")
    if (DEBUG)
      substitutedAST.prettyPrint("")
    if (unknown.length == 1) {
      val res = ModelReconstructor.getValue(substitutedAST, unknown.head, inputTheory)
      Some (unknown.head, res)
    } else
      None
  }
  
  def numUndefValues(candidateModel : Model, ast : AST) : Int = {
    val assigned = ast.children.filter(( a : AST) => candidateModel.contains(a))
    assigned.length      
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
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    //ModelReconstructor.reconstructNodeByNode(ast, decodedModel, reconstructNode)
    fixPointBasedReconstruction(ast, decodedModel)
  }
  
  def fixPointBasedReconstruction(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()  
    val atoms = retrieveCriticalAtoms(decodedModel)(ast)
    val vars = atoms.iterator.filter(_.isVariable)
    
    debug("Vars \n" + vars.mkString("\n "))
    
    initializeCandidateModel(atoms, decodedModel, candidateModel)
    
    //Fix-point computation
    var done = false
    var changed = false
    var iteration = 0
    while (! done) {
      iteration += 1
      verbose("Patching iteration " + iteration)
      val toVerify = atoms.filter { x => numUndefValues(candidateModel, x) == 0 }
      
      val implications = atoms.filter { x => numUndefValues(candidateModel, x) == 1 }
      verbose(implications.mkString(", "))
      
      changed = false
      for (i <- implications) {
        getImplication(candidateModel, i) match {
          case Some((node, value)) => {
            candidateModel.set(node, value)
            changed = true
          }
          case None => ()
        }
      }
      
      if (!changed) {
         val undefVars = vars.filter(candidateModel.contains(_)).toList
         if (undefVars.isEmpty) {
           done = true
         } else {
           val chosen =  chooseVar(atoms, undefVars)
           candidateModel.set(chosen, decodedModel(chosen))
         }
           
      }
    }
    
    for (node <- ast.iterator.toList.reverse) {
      if (!candidateModel.contains(node))
        reconstructNode(decodedModel, candidateModel, node)        
    }
    println(candidateModel)
    candidateModel
  }
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
    
    val nodesToRefine = booleanComparisonOfModels(ast, decodedModel, failedModel)
    
    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter( x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)).take(k)) { 
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1      
    }
    
    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      unsatRefine(ast, List(), pmap)
    }
    newPMap    
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    pmap.map(unsatRefinePrecision)
  }
  
  
  //******************************************************************//
  //                    Equality as Assignment                        //
  //******************************************************************//
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      case AST(fpEq : FloatingPointTheory.FPPredicateSymbol, path, children) 
        if (fpEq.getFactory == FloatingPointTheory.FPEqualityFactory 
            && decodedModel(ast).symbol == BoolTrue)  => {
         val lhs = children(0)
         val rhs = children(1)         
         val lhsDefined = candidateModel.contains(lhs)
         val rhsDefined = candidateModel.contains(rhs) 
         
         (lhs.isVariable, rhs.isVariable) match {
           case (true, true) => {
             (lhsDefined, rhsDefined) match {
               case (false, true) => candidateModel.set(lhs, candidateModel(rhs))
                                     true
               case (true, false) => candidateModel.set(rhs, candidateModel(lhs))
                                     true
               case (false, false) => false
               case (true, true) => false
             }
           }           
           case (true, false) if (!lhsDefined) => {
             candidateModel.set(lhs, candidateModel(rhs))
             true
           }
           case (false, true) if (!rhsDefined) =>{
             candidateModel.set(rhs, candidateModel(lhs))
             true
           }
           case (_, _) => false
        }
      }
      case _ => false
    }
  }
  
  // Helper functions
  
  // If the values has been used in the evaluation it is retrieved from the candidate model.
  // Otherwise, it is retrieved from the decoded model and stored in the candidate model,
  // since it is about to be used in evaluation.
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    } 
    candidateModel(ast)
  }
}
