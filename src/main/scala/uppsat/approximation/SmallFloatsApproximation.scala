package uppsat.approximation


import uppsat.theory.FloatingPointTheory._
import uppsat.Timer

import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.ModelReconstructor
import uppsat.ast.AST
import uppsat.ast._
import uppsat.solver.Z3Solver
import uppsat.solver.Z3OnlineSolver
import uppsat.theory.BooleanTheory.BoolTrue
import uppsat.theory.BooleanTheory.BoolFalse
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory.BooleanFunctionSymbol
import uppsat.theory.BooleanTheory.BooleanConstant
import uppsat.theory.BooleanTheory.BoolVar
import uppsat.ModelReconstructor.Model
import uppsat.solver.Z3OnlineException
import uppsat.solver.Z3OnlineSolver

object SmallFloatsApproximation extends NodeByNodeApproximation {
  // Input and output languages
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  
  //Precision type and ordering
  type P = Int  
  val precisionOrdering = new IntPrecisionOrdering(0, 5)
  
  val DEBUG = false

  // Parameters of satRefine, can be overriden to provide differen values
  val topK = 10 // K 
  val fractionToRefine = 0.3 //K_percentage
  val precisionIncrement = 1 // 20/100 = 1/5
  
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {
      val AST(symbol, label, children) = ast      
      var err = 0.0
      
      symbol match {
        case literal : FloatingPointLiteral => ()
        case fpfs : FloatingPointFunctionSymbol =>
          (decodedModel(ast).symbol, failedModel(ast).symbol)  match {
          case (approximate : FloatingPointLiteral, exact : FloatingPointLiteral) => {
            val outErr = relativeError(approximate, exact)
            
            var sumDescError = 0.0
            var numFPArgs = 0
            
            for (c <- children) {
              val a = decodedModel(c)
              val b = failedModel(c)
              
              (a.symbol, b.symbol) match {
                case (aS : FloatingPointLiteral, bS: FloatingPointLiteral) => {
                  sumDescError +=  relativeError(aS, bS)
                  numFPArgs += 1
                }                                                                 
                case  _ => ()
              }
            }
            val inErr = sumDescError / numFPArgs
            
            if (numFPArgs == 0) 
              err = outErr
            else
              err = outErr / inErr
          }
          case _ => ()
        }
        case _ => ()
      }
      
      
      if (err == 0.0)
        accu
      else
        accu + (ast -> err)
    }
  
  def satRefinePrecision( node : AST, pmap : PrecisionMap[Int]) : Int = {
    val p =  pmap(node.label)    
    val newP = (p + precisionIncrement) max p
    newP min pmap.precisionOrdering.maximalPrecision // TODO:  This check should be in the ordering somewhere?
  }
  
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
  
  
  def cast(ast : AST, target : ConcreteSort) : AST = {
    val source = ast.symbol.sort
    if (ast.symbol.sort != RoundingModeSort && source != target ) {      
      val cast = FPToFPFactory(List(ast.symbol.sort, target))
      val rtzNode = AST(RoundToZero, List(), List())
      AST(cast, List(), List(rtzNode, ast))
    } else {
      ast
    } 
  }
    
  def encodeNode(ast : AST, children : List[AST], precision : Int) : AST = {
      ast.symbol match {
      case fpLit : FloatingPointConstantSymbol => {
        ast 
      }
      
      case fpSym : FloatingPointFunctionSymbol => {
          val newSort = scaleSort(fpSym.sort, precision)
          val newChildren = 
            if (fpSym.getFactory == FPToFPFactory) {// No need to cast, this symbol does this!
              children
            } else {
              for ( c <- children) yield {
                 cast(c, newSort)                   
              }
            }
          val argSorts = newChildren.map( _.symbol.sort)
          AST(fpSym.getFactory(argSorts ++ List(newSort)), ast.label, newChildren) 
      }
      
      case fpPred : FloatingPointPredicateSymbol => {
        val newSort = children.tail.foldLeft(children.head.symbol.sort)((x,y) => if (compareSorts(x, y.symbol.sort)) x else  y.symbol.sort)
        val newChildren = 
          for ( c <- children) yield {
            cast(c, newSort)          
          }
        val argSorts = newChildren.map( _.symbol.sort)
        AST(fpPred.getFactory(argSorts ++ List(fpPred.sort)), ast.label, newChildren)
      }
      
      case fpVar : FPVar => {
        val newSort = scaleSort(fpVar.sort, precision)
        val newVar = FPVar(fpVar.name)(newSort)
        uppsat.ast.Leaf(newVar, ast.label)
      }
      
      case _ => {
        AST(ast.symbol, ast.label, children) 
      }
    }
  }
   
  
  def decodeNode( args : (Model, PrecisionMap[P]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    
    if (!appModel.contains(ast))
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
    val decodedValue = decodeSymbolValue(ast.symbol, appModel(ast), pmap(ast.label))
    
    if (decodedModel.contains(ast)){
      val existingValue = decodedModel(ast).symbol 
      if ( existingValue.toString() != decodedValue.symbol.toString()) {
         ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue.symbol)
      }
    } else {
      decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
  
  def reconstructNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
        
    if (!equalityAsAssignment(ast, decodedModel, candidateModel) && children.length > 0) {
      val newChildren = for ( c <- children) yield {        
        getCurrentValue(c, decodedModel, candidateModel)
      }
   
      //Evaluation
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelReconstructor.evalAST(newAST, FloatingPointTheory)
      if ( DEBUG && symbol.sort == BooleanTheory.BooleanSort) { // TODO: Talk to Philipp about an elegant way to do flags
        val assignments = candidateModel.getAssignmentsFor(ast).toList
        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
        
        val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
        if ( backupAnswer != answer )
          throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)

      }        
      candidateModel.set(ast, newValue)
    }
    candidateModel
  }
  
    
  // Helper functions  
  def compareSorts(s1 : Sort, s2 : Sort) = {
    (s1, s2) match {
      case (FPSort(eb1, sb1), FPSort(eb2, sb2)) => eb1 + sb1 > eb2 + sb2
      case (FPSort(_, _), _) | (_, FPSort(_, _)) => true        
    }
  }
  
  def scaleSort(sort : FPSort, p : Int) = {
    val eBits = 3 + ((sort.eBits - 3) * p)/precisionOrdering.maximalPrecision
    val sBits = 3 + ((sort.sBits - 3) * p)/precisionOrdering.maximalPrecision
    sort.getFactory(List(eBits, sBits))
  }
    
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), fp : FloatingPointTheory.FloatingPointLiteral)  => {
        val fullEBits = fp.eBits.head :: List.fill(e - fp.eBits.length)(0) ++ fp.eBits.tail
        val fullSBits = fp.sBits ++ List.fill((s - 1) - fp.sBits.length)(0)
        Leaf(FPLiteral(fp.sign, fullEBits, fullSBits, FPSort(e, s)))
      }
      
      case (FPSort(e, s), fp : FloatingPointTheory.FloatingPointConstantSymbol)  => {
        fp.getFactory match {
          case FPPlusInfinity => Leaf(FPPlusInfinity(List(FPSort(e, s))))
          case FPMinusInfinity => Leaf(FPMinusInfinity(List(FPSort(e, s))))
          case FPNaN => Leaf(FPNaN(List(FPSort(e, s))))
          case FPPositiveZero => Leaf(FPPositiveZero(List(FPSort(e, s))))
          case FPNegativeZero => Leaf(FPNegativeZero(List(FPSort(e, s))))
          case _ => throw new Exception("How do we translatee FPConstant Symbol? " + fp)
        }
      }      
      
      case _ => value
    }
  }  
  
  def relativeError(decoded : FloatingPointLiteral, precise : FloatingPointLiteral) : Double = {
    (decoded.getFactory, precise.getFactory) match {
      case (x, y) if (x == y) => 0.0 //Values are the same
      case (FPPlusInfinity, _)    |
           (_, FPPlusInfinity)    |
           (FPMinusInfinity, _)   |
           (_, FPMinusInfinity)   => Double.PositiveInfinity
      case (x : FPConstantFactory, y : FPConstantFactory) => {
        val a = bitsToDouble(decoded)
        val b = bitsToDouble(precise)
        Math.abs((a - b)/b)
      }        
      case _ => 0.0
    }
  }
}

