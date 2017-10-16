package uppsat.approximation

import uppsat.theory.Theory
import uppsat.ast.AST
import uppsat.ast.ConcreteSort
import uppsat.precision.PrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.ModelReconstructor.Model
import uppsat.ModelReconstructor
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


// Every approximation is  required to specify the:
// - an ordered finite height precision domain
// - input language of the constraints
// - output language of the constraints
trait ApproximationCore {
  val inputTheory : Theory
  val outputTheory : Theory

  type Precision
  val precisionOrdering : PrecisionOrdering[Precision]
}

// Approximation Codec :
// Encoding of formulas / Decoding of values / Ensuring well-sortedness

trait Codec extends ApproximationCore {
  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST
  def decodeModel(ast : AST, appMode : Model, pmap : PrecisionMap[Precision]) : Model
  // TODO: (Aleks) What is the purpose of this function. Casting things from A to B or B to A or both directions?
  def cast(ast : AST, target : ConcreteSort  ) : AST 


}

trait NodeByNodeCodec extends Codec {
  def encodeNode(ast : AST, children : List[AST], precision : Precision) : AST //Codec
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model

  def encodeFormula(ast : AST, pmap : PrecisionMap[Precision]) : AST = { 
    val AST(symbol, label, children) = ast
    val newChildren =
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }
    encodeNode(ast, newChildren, pmap(ast.label))
  }

  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Precision]) : Model = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
}

// ModelReconstructor?
// Uses various techniques to :
// - evaluate the decoded model in original semantics
// - patch / infer values where possible
object ModelReconstruction {
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
}

trait ModelReconstructor extends ApproximationCore {
  def reconstruct(ast : AST, decodedModel : Model) : Model
}
trait NodeByNodeReconstructor extends ModelReconstructor {
  def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy

  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, reconstructNode)
    reconstructedModel
  }

  // Utility function
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
      candidateModel.set(ast, decodedModel(ast))
    }
    candidateModel(ast)
  }
}
trait NumericModelLifting extends ModelReconstructor {

}

// Model reconstructor that uses EqualityAsAssignments
trait EqualityAsAssignmentReconstructor extends NodeByNodeReconstructor {
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      //        case AST(BoolEquality, _, _) |
      //             AST(IntEquality, _, _)|
      case AST(RoundingModeEquality, _ , _)|
          AST(_: FPPredicateSymbol, _, _)
          if (decodedModel(ast).symbol == BoolTrue &&
                (! ast.symbol.isInstanceOf[IndexedFunctionSymbol]
                   || ast.symbol.asInstanceOf[FPPredicateSymbol].getFactory == FPEqualityFactory)) => {
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

      //Evaluation
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelReconstructor.evalAST(newAST, inputTheory)
      // if ( globalOptions.PARANOID && symbol.sort == BooleanTheory.BooleanSort) {
      // TODO: Talk to Philipp about an elegant way to do flags
      // val assignments = candidateModel.variableAssignments(ast).toList
      //        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
      // val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
      // if ( backupAnswer != answer )
      //   throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)
      //
      //}
      candidateModel.set(ast, newValue)
    }
    candidateModel
  }
}


// Refinement strategy specifies how the precision mapping
// changes, based on a failed model or an unsatCore/proofOfUnsat
trait RefinementStrategy extends ApproximationCore {
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision]
  //    def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision]) : Precision
  //    def unsatRefinePrecision( p : Precision) : Precision

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

trait NodeByNodeRefinement extends RefinementStrategy {
  def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision]) : Precision
  def unsatRefinePrecision( p : Precision) : Precision

  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    val critical = ModelReconstruction.retrieveCriticalAtoms(decodedModel)(ast).map(_.iterator).flatten.toList
    val nodesToRefine = critical.filter( x => decodedModel(x) != failedModel(x))

    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter
         ( x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision))) {
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1
    }

    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    pmap.map(unsatRefinePrecision)
  }

}


// Error based refinement strategy uses a measure of error to
// determine which precisions need to be refined
// TODO: (Aleks) "Magic" numbers, I don't understand them
trait ErrorBasedRefinementStrategy extends NodeByNodeRefinement {
  val topK : Int // TODO: (Aleks) Should this be int or precision? RE: It should be int
  val fractionToRefine : Double
  val precisionIncrement : Precision

  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]
    override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])
      : PrecisionMap[Precision] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
      //    debug(errorRatios.mkString("\n"))
      //    debug(errorRatios.getClass)

    // TODO: (Aleks) Is this correct?ErrorBasedRefinementStrategy
    def compareFloatsWithSpecialNumbers(f1 : Double, f2: Double) : Boolean = {
      val d1 = f1.doubleValue()
      val d2 = f2.doubleValue()
      d1.compareTo(d2) > 0
    }

    val sortedErrRatios = errorRatios.toList.sortWith((x, y) => compareFloatsWithSpecialNumbers(x._2, y._2))
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions

    val relevantNodes = booleanComparisonOfModels(ast, decodedModel, failedModel)
    val nodesToRefine = sortedErrRatios.filter( x => relevantNodes.contains(x._1)).map(_._1)

    var newPMap = pmap
    var changes = 0
    for (node <-
         nodesToRefine.filter(
           x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)
         ).take(k)) {
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1
    }

    if (changes == 0) {
      // all the nodes where evaluation fails are at full precision.
      // UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap
  }
}

trait UniformRefinementStrategy extends RefinementStrategy {
  def increasePrecision(p : Precision) : Precision

  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])  = {
    pmap.map(increasePrecision)
  }
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    pmap.map(increasePrecision)
  }
}
