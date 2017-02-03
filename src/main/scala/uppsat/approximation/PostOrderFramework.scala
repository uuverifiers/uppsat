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
import uppsat.theory.BooleanTheory.BoolTrue

trait ApproximationCore {
  val inputTheory : Theory
  val outputTheory : Theory
  
  type Precision  
  val precisionOrdering : PrecisionOrdering[Precision]
  
  
}

trait ApproximationCodec extends ApproximationCore {
  def encodeNode(ast : AST, children : List[AST], precision : Precision) : AST //Codec
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model
  def cast(ast : AST, target : ConcreteSort  ) : AST // PrecisionOrdering ?
}

trait Reconstructor extends ApproximationCore {
  def evaluateNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy  
  
  // Utility function
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    } 
    candidateModel(ast)
  }
}

// This one could maybe be interleaved with the evaluation function provided buy
// approximation bundle
trait EqualityAsAssignmentReconstructor extends Reconstructor {
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      case AST(fpEq : FloatingPointTheory .FPPredicateSymbol, path, children) 
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
}

trait RefinementStrategy extends ApproximationCore {  
  def satRefinePrecision( node : AST, pmap : PrecisionMap[Precision]) : Precision
  def unsatRefinePrecision( p : Precision) : Precision
}

trait ErrorBasedRefinementStrategy extends RefinementStrategy {
  val topK : Int
  val fractionToRefine : Double 
  val precisionIncrement : Precision
  
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]  
}


class PostOrderNodeBasedApproximation(val appCore : ApproximationCore with ApproximationCodec with Reconstructor with ErrorBasedRefinementStrategy  ) extends Approximation {
  
  type P = appCore.Precision
  val precisionOrdering = appCore.precisionOrdering
  val inputTheory = appCore.inputTheory
  val outputTheory = appCore.outputTheory
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }    
    appCore.encodeNode(ast, newChildren, pmap(ast.label))    
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), appCore.decodeNode)
    decodedModel
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()    
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, appCore.evaluateNode)
    reconstructedModel
  }
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, appCore.nodeError(decodedModel)(failedModel))
    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
    val k = math.ceil(appCore.fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
 
    def booleanComparisonOfModels(ast : AST, decodedModel : Model, failedModel : Model) : List[AST] = {
      def boolCond( accu : List[AST], ast : AST) : Boolean = {
        decodedModel(ast) != failedModel(ast)
      }
      
      def boolWork( accu : List[AST], ast : AST) : List[AST] = {      
        ast :: accu
      }
      
      AST.boolVisit(ast, List(), boolCond, boolWork).toSet.toList
    }
    
    val nodesToRefine = booleanComparisonOfModels(ast, decodedModel, failedModel)
    
    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter( x => appCore.precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)).take(k)) { 
      newPMap = newPMap.update(node.label, appCore.satRefinePrecision(node, newPMap))
      changes += 1      
    }
    
    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = unsatRefine(ast, List(), pmap)
    }
    newPMap    
  }
  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    pmap.map(appCore.unsatRefinePrecision)
  }


}