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
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      //        case AST(BoolEquality, _, _) |
      //             AST(IntEquality, _, _)|
      case AST(RoundingModeEquality, _ , _)|
          AST(_: FPPredicateSymbol, _, _)
          if (decodedModel(ast).symbol == BoolTrue &&
                (! ast.symbol.isInstanceOf[IndexedFunctionSymbol]
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPEqualityFactory
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPFPEqualityFactory)) => {
            val lhs = ast.children(0)
            val rhs = ast.children(1)
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

  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast

    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {
        getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      candidateModel.set(ast, newValue)
    }
    candidateModel
  }
}