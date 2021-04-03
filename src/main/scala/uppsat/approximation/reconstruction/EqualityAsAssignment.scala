package uppsat.approximation.reconstruction


import scala.collection.mutable.{ListBuffer, MultiMap, Queue, Set, Stack}

import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation.ModelReconstruction
import uppsat.approximation.toolbox.Toolbox
import uppsat.globalOptions
import uppsat.globalOptions._
import uppsat.ast.{AST, ConcreteFunctionSymbol, IndexedFunctionSymbol}
import uppsat.theory.BooleanTheory._
import uppsat.theory.BooleanTheory.BoolEquality
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.IntegerTheory.{IntegerPredicateSymbol, IntEquality}


/** Reconstruction using equality as assignment */
trait EqualityAsAssignmentReconstruction extends ModelReconstruction {

  /**
    * Tries to apply the equality-as-assignment heuristic, returning true if
    * successful (else otherwise) Checks whether the root node of the AST is an
    * equality. If so, if one of the sides is an undefined variable, that
    * variables will be assigned the expression of the other side in
    * candidateModel.
    *
    * Note: If the root node of ast is an equality it has to be defined in the
    * decodedModel.
    *
    * @param ast The node to which equality-as-assignment should be applied
    * (node of the full-precision formula)
    * @param decodedModel The model of the approximate formula
    * @param candidateModel The potential model which is under construction (of
    * the full-precision formula), will be updated if equality-as-assignment is
    * applied.
    *
    * @return True if equalityAsAssignment could be applied, otherwise false
    */
  def equalityAsAssignment(ast : AST,
                           decodedModel : Model,
                           candidateModel : Model) : Boolean = {
    ast match {
      case AST(RoundingModeEquality, _ , _)|
           AST(BoolEquality, _, _) |
           AST(IntEquality, _, _)|
           AST(_: FPPredicateSymbol, _, _)
           if (decodedModel(ast).symbol == BoolTrue &&
                (!ast.symbol.isInstanceOf[IndexedFunctionSymbol] ||
                   ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory ==
                   FPEqualityFactory ||
                   ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory ==
                   FPFPEqualityFactory)) => {
            val (lhs, rhs) = (ast.children(0), ast.children(1))
             val (lhsDefined, rhsDefined) =
               (candidateModel.contains(lhs), candidateModel.contains(rhs))

            ((lhs.isVariable, lhsDefined), (rhs.isVariable, rhsDefined)) match {
              case ((true, false), (true, true)) => {
                candidateModel.set(lhs, candidateModel(rhs))
                candidateModel.set(ast, BoolTrue)
                true
              }
              case ((true, true), (true, false)) => {
                candidateModel.set(rhs, candidateModel(lhs))
                candidateModel.set(ast, BoolTrue)
                true
              }
              case ((true, false), (false, _)) => {
                candidateModel.set(lhs, candidateModel(rhs))
                candidateModel.set(ast, BoolTrue)
                true
              }
              case ((false, _), (true, false)) => {
                candidateModel.set(rhs, candidateModel(lhs))
                candidateModel.set(ast, BoolTrue)
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

  def reconstructNode(decodedModel  : Model,
                      candidateModel : Model,
                      ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    if (children.length > 0 &&
          !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for (c <- children) yield {
        Toolbox.getCurrentValue(c, decodedModel, candidateModel)
      }

      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelEvaluator.evalAST(newAST, inputTheory)
      verbose(ast.symbol + " " + ast.label + " " + " <- " + newValue.symbol)

      candidateModel.set(ast, newValue)
      candidateModel
    } else {
      candidateModel
    }
  }

  def reconstructSubtree(ast : AST,
                         decodedModel : Model,
                         candidateModel : Model) : Model = {
    AST.postVisit[Model, Model](ast,
                                candidateModel,
                                decodedModel,
                                reconstructNode)
    candidateModel
  }

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val candidateModel = new Model()

    val todo = new Stack[AST]()
    todo.push(ast)

    val toEvaluateEquality = ListBuffer() : ListBuffer[AST]
    val toEvaluateBoolean = new Stack[AST]()
    val toReconstructPredicate = new Queue[AST]()

    // Traverse the tree and add all nodes to respective list
    while (!todo.isEmpty) {
      val nextItem = todo.pop()
      (nextItem.symbol) match {
       case (RoundingModeEquality) |
            FPEqualityFactory(_) |
            FPFPEqualityFactory(_) => {
            toEvaluateEquality += nextItem
            }

       case intPred : IntegerPredicateSymbol => {
         toReconstructPredicate += nextItem
       }

       case fpPred : FloatingPointPredicateSymbol => {
         toReconstructPredicate += nextItem
       }

       case _ if nextItem.symbol.sort == BooleanSort => {
         toEvaluateBoolean.push(nextItem)
          for (c <- nextItem.children)
            todo.push(c)
        }
      }
    }

    val equalitySort =
      Toolbox.topologicalSortEqualities(toEvaluateEquality.toList)

    equalitySort.map(reconstructSubtree(_, decodedModel, candidateModel))
    toReconstructPredicate.map{
      reconstructSubtree(_, decodedModel, candidateModel)
    }
    toEvaluateBoolean.map(reconstructNode(decodedModel, candidateModel, _))
    candidateModel
  }
}
