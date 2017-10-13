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
  trait ApproximationCodec extends ApproximationCore {
    def encodeNode(ast : AST, children : List[AST], precision : Precision) : AST //Codec
    def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model
    
    // TODO: (Aleks) What is the purpose of this function. Casting things from A to B or B to A or both directions?
    def cast(ast : AST, target : ConcreteSort  ) : AST // PrecisionOrdering ?
  }
  
  // ModelReconstructor? 
  // Uses various techniques to : 
  // - evaluate the decoded model in original semantics
  // - patch / infer values where possible
  trait NodeByNodeReconstructor extends ApproximationCore {
    def evaluateNode( decodedM : Model,  candidateM : Model, ast :  AST) : Model //satisfy  
    
    // Utility function
    def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
      if (! candidateModel.contains(ast)) {
            candidateModel.set(ast, decodedModel(ast))
      } 
      candidateModel(ast)
    }
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
    
    def evaluateNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
        val AST(symbol, label, children) = ast
        
        if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
          val newChildren = for ( c <- children) yield {        
            getCurrentValue(c, decodedModel, candidateModel)
          }
       
          //Evaluation
          val newAST = AST(symbol, label, newChildren.toList)
          val newValue = ModelReconstructor.evalAST(newAST, inputTheory)
    //      if ( globalOptions.PARANOID && symbol.sort == BooleanTheory.BooleanSort) { // TODO: Talk to Philipp about an elegant way to do flags
    //        val assignments = candidateModel.variableAssignments(ast).toList
    //        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
    //        
    //        val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
    //        if ( backupAnswer != answer )
    //          throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)
    //
    //      }        
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
  }
  
  // Error based refinement strategy uses a measure of error to 
  // determine which precisions need to be refined
  // TODO: (Aleks) "Magic" numbers, I don't understand them
  trait ErrorBasedRefinementStrategy extends RefinementStrategy {
    val topK : Precision // TODO: (Aleks) Should this be int or precision?
    val fractionToRefine : Double 
    val precisionIncrement : Precision

    def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision]) : Precision
    def unsatRefinePrecision( p : Precision) : Precision    
    
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
    println(errorRatios.mkString("\n"))
    println(errorRatios.getClass)
    
    // TODO: (Aleks) Is this correct?ErrorBasedRefinementStrategy
    def compareFloatsWithSpecialNumbers(f1 : Double, f2: Double) : Boolean = {
      val d1 = f1.doubleValue()
      val d2 = f2.doubleValue()
      d1.compareTo(d2) > 0
    }
    
    val sortedErrRatios = errorRatios.toList.sortWith((x, y) => compareFloatsWithSpecialNumbers(x._2, y._2))
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
 
    def booleanComparisonOfModels(ast : AST, decodedModel : Model, failedModel : Model) : List[AST] = {
      def boolCond( accu : List[AST], ast : AST) : Boolean = {
        decodedModel(ast) != failedModel(ast)
      }
      
      def boolWork( accu : List[AST], ast : AST) : List[AST] = {      
        ast :: accu
      }
      
      AST.boolVisit(ast, List(), boolCond, boolWork).toSet.toList
    }
    
    val relevantNodes = booleanComparisonOfModels(ast, decodedModel, failedModel)
    val nodesToRefine = sortedErrRatios.filter( x => relevantNodes.contains(x._1)).map(_._1)
    
    var newPMap = pmap
    var changes = 0
    for (node <- nodesToRefine.filter( x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)).take(k)) { 
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
    
    
    def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double]  
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
  