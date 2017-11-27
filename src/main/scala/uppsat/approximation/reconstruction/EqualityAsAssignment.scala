package uppsat.approximation.reconstruction

import uppsat.globalOptions._
import uppsat.approximation.ModelReconstruction
import scala.collection.mutable.{ListBuffer, Set}
import uppsat.ast.ConcreteFunctionSymbol
import scala.collection.mutable.{HashMap, MultiMap}

import uppsat.ast.AST
import uppsat.ast.IndexedFunctionSymbol

import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model

import uppsat.theory.FloatingPointTheory
import uppsat.theory.BooleanTheory._
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.IntegerTheory.IntEquality
import uppsat.theory.FloatingPointTheory.RoundingModeEquality
import uppsat.theory.FloatingPointTheory.FPPredicateSymbol
import uppsat.theory.FloatingPointTheory.FPEqualityFactory
import uppsat.theory.FloatingPointTheory.FPFPEqualityFactory
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort

import uppsat.approximation.toolbox.Toolbox

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import uppsat.theory.FloatingPointTheory.FloatingPointPredicateSymbol
import uppsat.globalOptions


trait EqualityAsAssignmentReconstruction extends ModelReconstruction {
  
  
 def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match { 
      case AST(RoundingModeEquality, _ , _)|
           AST(BoolEquality, _, _) | 
           AST(IntEquality, _, _)|       
           AST(_: FPPredicateSymbol, _, _) 
           if (decodedModel(ast).symbol == BoolTrue && 
                (! ast.symbol.isInstanceOf[IndexedFunctionSymbol] 
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPEqualityFactory 
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPFPEqualityFactory)) => { 
            val (lhs, rhs) = (ast.children(0), ast.children(1))
            val (lhsDefined, rhsDefined) = (candidateModel.contains(lhs), candidateModel.contains(rhs))

            ((lhs.isVariable, lhsDefined), (rhs.isVariable, rhsDefined)) match {
              case ((true, false), (true, true)) => {
                candidateModel.set(lhs, candidateModel(rhs)) 
                true                
              }
              case ((true, true), (true, false)) => {
                candidateModel.set(rhs, candidateModel(lhs)) 
                true                
              }              
              case ((true, false), (false, _)) => {
                candidateModel.set(lhs, candidateModel(rhs)) 
                true                 
              }
              case ((false, _), (true, false)) => {
                candidateModel.set(rhs, candidateModel(lhs)) 
                true                 
              }              
              case (_, _) => {
                false 
              }
            }
        }
      case _ => false
    }
 }
            
            
  
  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }
      
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(ast.symbol + " " + ast.label + " " + " <- " + newValue.symbol)
      
      candidateModel.set(ast, newValue)      
      
      if(globalOptions.VERBOSE)
        ast.ppWithModels("", decodedModel, candidateModel, false)
    }
    candidateModel
  }
  
  def reconstructSubtree(ast : AST, decodedModel : Model, candidateModel : Model) : Model = {
    AST.postVisit[Model, Model](ast, candidateModel, decodedModel, reconstructNode)
    candidateModel
  }
  
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()
    
    val todo = new Stack[AST]()
    val toEvaluateEquality = ListBuffer() : ListBuffer[AST]
    val toEvaluateBoolean = new Stack[AST]()
    val toReconstructPredicate = new Queue[AST]()
    todo.push(ast)
    
     
    
    while (!todo.isEmpty) {
      val nextItem = todo.pop()
      (nextItem.symbol) match {
        
       case (RoundingModeEquality)| 
            (FPEqualityFactory(_)) |
            (FPFPEqualityFactory(_)) => {
            toEvaluateEquality += nextItem //reconstructSubtree(nextItem, decodedModel, candidateModel)
        }
        
       case fpPred : FloatingPointPredicateSymbol => {
         toReconstructPredicate += nextItem
       }
            
       // Check if this node is actually true
       case _ if nextItem.symbol.sort == BooleanSort => {
         toEvaluateBoolean.push(nextItem)
          for (c <- nextItem.children)
            todo.push(c)
        }
        
      }
    }
      
    val equalitySort = Toolbox.topologicalSortEqualities(toEvaluateEquality.toList)
        
    equalitySort.map(reconstructSubtree(_, decodedModel, candidateModel))
    toReconstructPredicate.map(reconstructSubtree(_, decodedModel, candidateModel))
    toEvaluateBoolean.map(reconstructNode(decodedModel, candidateModel, _))
    candidateModel
    
  }  
}
