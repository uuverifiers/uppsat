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
    val unassigned = ast.children.filterNot(candidateModel.contains(_))
    unassigned.length      
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
         val undefVars = vars.filterNot(candidateModel.contains(_)).toList
         if (undefVars.isEmpty) {
           done = true
         } else {
           val chosen =  chooseVar(atoms, undefVars)
           candidateModel.set(chosen, decodedModel(chosen))
         }
           
      }
    }
    
    def copyFromDecodedModelIfNotSet (decodedModel : Model, candidateModel : Model, ast : AST) = {
      if (! candidateModel.contains(ast)) {
            candidateModel.set(ast, decodedModel(ast))
      }
      candidateModel
    }
    
    AST.postVisit(ast, candidateModel, decodedModel, copyFromDecodedModelIfNotSet)
    candidateModel
  }
  
}