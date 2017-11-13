package uppsat.approximation.reconstruction

import uppsat.globalOptions._
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


trait EqualityAsAssignmentReconstruction extends PostOrderReconstruction {
  
  def trySet(lhs : AST, rhs : AST, candidateModel : Model) : Boolean = {
    val lhsDefined = candidateModel.contains(lhs)
    val rhsDefined = candidateModel.contains(rhs)
  
    val ret = 
      (lhs.isVariable, rhs.isVariable) match {
        case (true, true) => {
          (lhsDefined, rhsDefined) match {
            case (false, true) => {
              verbose(">> " + lhs.symbol + " " + lhs.label + " " + " <- " + candidateModel(rhs).symbol + "/" + rhs.symbol + " " + rhs.label + "/")  
              candidateModel.set(lhs, candidateModel(rhs))
              true
            }
            case (true, false) => {
              verbose(">> " + rhs.symbol + " " + rhs.label + " " + " <- " + candidateModel(lhs).symbol + "/" + lhs.symbol + " " + lhs.label + "/")
              candidateModel.set(rhs, candidateModel(lhs))
              true
            }
            case (false, false) => {
              false
            }
            case (true, true) => {
              false
            }
          }
        }
        case (true, false) if (!lhsDefined) => {
          verbose(">> " + lhs.symbol + " " + lhs.label + " " + " <- " + candidateModel(rhs).symbol + "/" + rhs.symbol + " " + rhs.label + "/")
          candidateModel.set(lhs, candidateModel(rhs))
          true
        }
        case (false, true) if (!rhsDefined) =>{
          verbose(">> " + rhs.symbol + " " + rhs.label + " " + " <- " + candidateModel(lhs).symbol + "/" + lhs.symbol + " " + lhs.label + "/")
          candidateModel.set(rhs, candidateModel(lhs))
          true
        }
        case (_, _) => {
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
          case other => false
        } 
      } else {
        false
      }
    if (ret) {
      verbose("> " + ast.symbol + " " + ast.label + " " + " <- " + BoolTrue)
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
      println("-----------------")
      verbose(ast.symbol + " " + ast.label + " " + " <- " + newValue.symbol)
      candidateModel.set(ast, newValue)      
//      ast.ppWithModels("", decodedModel, candidateModel, false)
//      println("-----------------")
    }
    candidateModel
  }
}