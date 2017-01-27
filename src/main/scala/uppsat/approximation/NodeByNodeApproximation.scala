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
import uppsat.theory.FloatingPointTheory.FPEqualityFactory // TODO: isEquality method should be added so that Equality as assignment is not tied to any particular Theory
import uppsat.theory.FloatingPointTheory

trait NodeByNodeApproximation extends Approximation {  
  def encodeNode(ast : AST, children : List[AST], precision : P) : AST
  def decodeNode( args : (Model, PrecisionMap[P]), decodedModel : Model, ast : AST) : Model
  def reconstructNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model 
  def cast(ast : AST, target : ConcreteSort  ) : AST // PrecisionOrdering ? 
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]
  def satRefinePrecision( node : AST, pmap : PrecisionMap[P]) : P
  def unsatRefinePrecision( p : P) : P
  
  
  //Parameters for SAT refinement 
  val topK : Int
  val fractionToRefine : Double 
  val precisionIncrement : P
    
  def encodeFormula(ast : AST, pmap : PrecisionMap[P]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeFormula( c, pmap)
      }    
    encodeNode(ast, newChildren, pmap(ast.label))    
  }
  
  def booleanComparisonOfModels(ast : AST, decodedModel : Model, failedModel : Model) : List[AST] = {
      def boolCond( accu : List[AST], ast : AST, path : Path) : Boolean = {
        decodedModel(ast) != failedModel(ast)
      }
      
      def boolWork( accu : List[AST], ast : AST) : List[AST] = {      
        ast :: accu
      }
      
      AST.boolVisit(ast, List(), boolCond, boolWork).toSet.toList
  }
  
  // Relies on decodeNode method being supplied by the user
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[P]) = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()    
    AST.postVisit[Model, Model](ast, reconstructedModel, decodedModel, reconstructNode)
    reconstructedModel
  }
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
    
    val nodesToRefine = booleanComparisonOfModels(ast, decodedModel, failedModel)
    
    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter( x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)).take(k)) { 
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap))
      changes += 1      
    }
    
    if (changes == 0) { // This could actually happen, that all the nodes where evaluation fails are at full precision. UnsatRefine in that case.
      unsatRefine(ast, List(), pmap)
    }
    newPMap    
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[P]) : PrecisionMap[P] = {
    pmap.map(unsatRefinePrecision)
  }
  
  
  //******************************************************************//
  //                    Equality as Assignment                        //
  //******************************************************************//
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      case AST(fpEq : FloatingPointTheory.FPPredicateSymbol, path, children) 
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
  
  // Helper functions
  
  // If the values has been used in the evaluation it is retrieved from the candidate model.
  // Otherwise, it is retrieved from the decoded model and stored in the candidate model,
  // since it is about to be used in evaluation.
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
    } 
    candidateModel(ast)
  }
}
