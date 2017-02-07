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
    val vars = ast.iterator.toList.filter(_.isVariable)
    
    val assertions : List[(ConcreteFunctionSymbol, AST)] = 
      for ( v <- vars if(candidateModel.contains(v))) yield {        
          (v.symbol, candidateModel(v))
      }
    
    val unknown = vars.filterNot(candidateModel.contains(_)).map(_.symbol).distinct
    
    
    if (unknown.length > 1) 
      throw new Exception("getImplication assumes at most one unknown" + unknown.mkString(", "))
    
    
    if (unknown.length == 1) {
      val res = ModelReconstructor.evalAST(ast, unknown.head, assertions, inputTheory)
      Some (unknown.head, res)
    } else
      None
    None
  }
  
  def numUndefValues(candidateModel : Model, ast : AST) : Int = {
//    /println("Children \n\t")
//    var unassigned = 0
//    for (c <- ast.children) {
//      if (candidateModel.contains(c)) 
//        println("\t" + c + " already present in candidate model with " + candidateModel(c))
//      else {
//        println("\t" + c + " not present in candidate model")
//        unassigned += 1
//      } 
//    }
    val unassigned = ast.iterator.toList.filter((x:AST) => (x.children.length == 0) && !candidateModel.contains(x))
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
    val terms = atoms.map(_.iterator.toList).flatten 
    val vars = terms.filter(_.isVariable).toSet.toList
    
    verbose("Starting fixpoint reconstruction")
    verbose("Atoms(" + atoms.length + "):\n\t" + atoms.mkString("\n\t"))
    verbose("Vars(" + vars.length + "):\n\t" + vars.mkString("\n\t"))
    
    
    
    initializeCandidateModel(atoms, decodedModel, candidateModel)
    
    //Fix-point computation
    var done = false
    var changed = false
    var iteration = 0
    while (! done) {
      iteration += 1
      verbose("=============================\nPatching iteration " + iteration)
      
      
      val implications = atoms.filter { x => x.children.length > 0 && numUndefValues(candidateModel, x) == 1 }
      verbose("Implications(" + implications.length + "):\n\t" + implications.mkString("\n\t"))
      
      changed = false
      for (i <- implications) {
        val imp = getImplication(candidateModel, i) 
        verbose("Chosen - " + imp)
        imp match {
          case Some((node, value)) => {
            verbose("Adding " + node + " -> " + value)
            candidateModel.set(node, value)
            changed = true
          }
          case None => {
            if (! candidateModel.contains(ast)) {
              candidateModel.set(ast, decodedModel(ast))
              changed = true
            }
          }
        }
      }
      
      if (!changed) {
         verbose("No implications ... ")
         val undefVars = vars.filterNot(candidateModel.contains(_)).toList
         if (undefVars.isEmpty) {
           verbose("No undefined variables ...\n Done satisfying critical atoms.")
           done = true
         } else {
           val chosen =  chooseVar(atoms, undefVars)
           verbose("Copying from decoded model " + chosen + " -> " + decodedModel(chosen))
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
    verbose("Completing the model")
    AST.postVisit(ast, candidateModel, decodedModel, copyFromDecodedModelIfNotSet)
    candidateModel
  }
  
}