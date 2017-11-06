package uppsat.approximation.toolbox


import uppsat.approximation._
import uppsat.theory.Theory
import uppsat.ast.AST
import uppsat.ast.ConcreteSort
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
import uppsat.theory.FloatingPointTheory.RoundingModeEquality
import uppsat.theory.FloatingPointTheory.FPPredicateSymbol
import uppsat.theory.FloatingPointTheory.FPEqualityFactory
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
}