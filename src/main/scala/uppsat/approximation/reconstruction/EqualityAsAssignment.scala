package uppsat.approximation.reconstruction

import uppsat.ast.AST

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
import uppsat.ast.IndexedFunctionSymbol

trait EqualityAsAssignmentReconstruction extends PostOrderReconstruction {
  
  def trySet(lhs : AST, rhs : AST, candidateModel : Model) : Boolean = {
    val lhsDefined = candidateModel.contains(lhs)
    val rhsDefined = candidateModel.contains(rhs)
  
    val ret = 
      (lhs.isVariable, rhs.isVariable) match {
        case (true, true) => {
          (lhsDefined, rhsDefined) match {
            case (false, true) => {
              candidateModel.set(lhs, candidateModel(rhs))
              true
            }
            case (true, false) => {
              candidateModel.set(rhs, candidateModel(lhs))
              true
            }
            case (false, false) => {
              println("trySet: " + lhs + " := "  + rhs)              
              println("\t\tCase 1.3")
              false
            }
            case (true, true) => {
              println("trySet: " + lhs + " := "  + rhs)              
              println("\t\tCase 1.4")
              false
            }
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
        case (_, _) => {
          println("trySet: " + lhs + " := "  + rhs)          
          println("\tCase 4 " + ((lhsDefined, rhsDefined)))
          false
        }
    }
    ret
    
  }
  
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    val ret = 
      if (ast.symbol.sort == BooleanSort && decodedModel(ast).symbol == BoolTrue) { 
        ast.symbol match {
          case RoundingModeEquality => trySet(ast.children(0), ast.children(1), candidateModel)
          case fpPred : FPPredicateSymbol => trySet(ast.children(0), ast.children(1), candidateModel)
          case idxSym : IndexedFunctionSymbol => 
            if (idxSym.getFactory == FPEqualityFactory || idxSym.getFactory == FPFPEqualityFactory)
              trySet(ast.children(0), ast.children(1), candidateModel)
            else
              false
          case BoolEquality => trySet(ast.children(0), ast.children(1), candidateModel)
          case BoolNegation | _ : NaryConjunction => false
          case other => throw new Exception("Unhandled Bool expresion in equalityAsAsssignment: " + other)
        } 
      } else {
        false
      }
    if (ret) {
      candidateModel.set(ast, BoolTrue)
    }
    ret
  }

  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {
        getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      println("\t" + newValue)
      candidateModel.set(ast, newValue)
    }
    candidateModel
  }
}