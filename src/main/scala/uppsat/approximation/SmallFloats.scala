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
import uppsat.globalOptions

trait SmallFloatsCore extends ApproximationCore {
   type Precision = Int
   val precisionOrdering = new IntPrecisionOrdering(0,5)
   val inputTheory = FloatingPointTheory
   val outputTheory = FloatingPointTheory   
}

  /**
   * The core of the smallfloats approximation!
	 * Other approximations might add top level constraints over the domain rather than 
   * change the sorts of the formula itself.
	 */

trait SmallFloatsCodec extends SmallFloatsCore with ApproximationCodec {

  class SmallFloatsException(msg : String) extends Exception("SmallFloats: " + msg)
  
  /**
   * Scales sort according to the precision p
	 *  
   * @param sort is the full precision sort which will be scaled down.
   * @param p is the precision used to calculate the new sort.
   * 
   * @return sort scaled down according to p 
	 */
  def scaleSort(sort : FPSort, p : Int) = {
    val eBits = 3 + ((sort.eBitWidth - 3) * p)/precisionOrdering.maximalPrecision
    val sBits = 3 + ((sort.sBitWidth - 3) * p)/precisionOrdering.maximalPrecision
    sort.getFactory(List(eBits, sBits))
  }

  /**
   * Checks whether s1 greater than s2 (i.e. has more number of bits).
	 *  
   * @param s1 first sort.
   * @param s2 second sort.
   * 
   * @return true if s1 has more bits than s2.
	 */  
  def sortGreaterThan(s1 : Sort, s2 : Sort) = {
    (s1, s2) match {
      case (FPSort(eb1, sb1), FPSort(eb2, sb2)) => eb1 + sb1 > eb2 + sb2
      case (FPSort(_, _), _) | (_, FPSort(_, _)) =>
        // TODO: (Aleks) I do not understand what this case is? This case used to return true
        throw new SmallFloatsException("Comparing FPSort with non-FPSort (" + s1 + ") & (" + s2 + ")")
    }
  }
  
  /**
   * Creates a new AST casting to target .
	 *  
	 *  Creates a new AST identical to ast with the possible addition of a
	 *  casting node at the root if ast is not of sort target. If the ast is not
	 *  of a FPSort, it is returned as-is.
	 *  
   * @param ast The AST to be casted.
   * @param target The sort to which ast is casted.
   * 
   * @return ast if sort of ast is target, otherwise ast with a new root node which casts ast to target sort. 
	 */
  def cast(ast : AST, target : ConcreteSort) : AST = {
    val source = ast.symbol.sort
    // TODO: (Aleks) Can we change these conditions. Why checking that it is not a RMSort instead of checking it is a FPSort?
    //if (ast.symbol.sort != RoundingModeSort && source != target ) {
    ast.symbol.sort match {
      case FPSort(_, _) if ast.symbol.sort != target => {
        val cast = FPToFPFactory(List(ast.symbol.sort, target))
        val rtzNode = AST(RoundToZero, List(), List())
        AST(cast, List(), List(rtzNode, ast))        
      }
      case _ => ast
    } 
  }  
   
  /** Encodes a node by scaling its sort based on precision and calling cast to ensure sortedness.
   *  
   *  @param ast Node of ast to encode.
   *  @param precision Precision to encode
   *  
   *  @return ast encoded according to precision.
   */
  def encodeNode(ast : AST, children : List[AST], precision : Int) : AST = {
      ast.symbol match {
      case _ : FloatingPointConstantSymbol => ast 
      
      // TODO: (Aleks) For fpSym we are just scaling the sort to get newSort, while in fpPred we are checking the children?
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
        val newSort = children.tail.foldLeft(children.head.symbol.sort)((x,y) => if (sortGreaterThan(x, y.symbol.sort)) x else  y.symbol.sort)
        val newChildren = 
          for ( c <- children) yield {
            cast(c, newSort)          
          }
        val argSorts = newChildren.map( _.symbol.sort)
        AST(fpPred.getFactory(argSorts ++ List(fpPred.sort)), ast.label, newChildren)
      }
      
      case fpVar : FPVar => {
        val newSort = scaleSort(fpVar.sort, precision)
        val newVar = FPVar(fpVar.name, newSort)
        uppsat.ast.Leaf(newVar, ast.label)
      }
      
      case _ => AST(ast.symbol, ast.label, children) 
    }
  }
  
  /** Decodes an approximative model value back to full precision.
   *  
   *  @param symbol A symbol representing the full precision sort.
   *  @param value The value to be converted.
   *  @param p The precision to which value was encoded.
   *  
   *  @return value decoded to the sort of symbol if it was encoded by precision p.
   */  
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), fp : FloatingPointTheory.FloatingPointLiteral) => {
        fp.getFactory match {
          case FPPlusInfinity => Leaf(FPPlusInfinity(List(FPSort(e, s))))
          case FPMinusInfinity => Leaf(FPMinusInfinity(List(FPSort(e, s))))
          case FPNaN => Leaf(FPNaN(List(FPSort(e, s))))
          case FPPositiveZero => Leaf(FPPositiveZero(List(FPSort(e, s))))
          case FPNegativeZero => Leaf(FPNegativeZero(List(FPSort(e, s))))
          case _ => {
            // When padding exponent, we retain the bias bit in the first position,
            // pad with zeroes and retain the value of the small exponent.
            val fullEBits = fp.eBits.head :: List.fill(e - fp.eBits.length)(0) ++ fp.eBits.tail
            // Padding significant is trivial, just adding the zero bits in lowest positions 
            val fullSBits = fp.sBits ++ List.fill((s - 1) - fp.sBits.length)(0)
            Leaf(FloatingPointLiteral(fp.sign, fullEBits, fullSBits, FPSort(e, s)))
          }
        }
      }      
      //  }
      case _ => value
    }
  }
  
  // decodes values associated with nodes in the formula.
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    
    // TEMPORARY TODO: FIX!
    val newAST = 
      if (FloatingPointTheory.isVariable(ast.symbol))    
        encodeNode(ast, List(), pmap(ast.label))
      else
        ast
    
    if (!appModel.contains(newAST))
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
    val decodedValue = decodeSymbolValue(ast.symbol, appModel(newAST), pmap(ast.label))
    
    if (decodedModel.contains(ast)){
      val existingValue = decodedModel(ast).symbol 
      if ( existingValue != decodedValue.symbol) {
        ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue.symbol)
      }
    } else {
      decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
}

trait SmallFloatsReconstructor extends EqualityAsAssignmentReconstructor {
  def evaluateNode( decodedModel  : Model, candidateModel : Model, ast : AST) : Model = {
    val AST(symbol, label, children) = ast
    
    if (children.length > 0 && !equalityAsAssignment(ast, decodedModel, candidateModel)) {
      val newChildren = for ( c <- children) yield {        
        getCurrentValue(c, decodedModel, candidateModel)
      }
   
      //Evaluation
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelReconstructor.evalAST(newAST, inputTheory)
      if ( globalOptions.PARANOID && symbol.sort == BooleanTheory.BooleanSort) { // TODO: Talk to Philipp about an elegant way to do flags
        val assignments = candidateModel.variableAssignments(ast).toList
        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
        
        val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
        if ( backupAnswer != answer )
          throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)

      }        
      candidateModel.set(ast, newValue)
    }
    candidateModel
  }
}

trait SmallFloatsRefinementStrategy extends SmallFloatsCore with ErrorBasedRefinementStrategy {
  val topK = 10 // K 
  val fractionToRefine = 1.0//K_percentage
  val precisionIncrement = 1 // 20/100 = 1/5

  def satRefinePrecision( node : AST, pmap : PrecisionMap[Int]) : Int = {
    val p =  pmap(node.label)    
    val newP = (p + precisionIncrement) max p
    newP min pmap.precisionOrdering.maximalPrecision // TODO:  This check should be in the ordering somewhere?
  }
  
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
  
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

object IJCARSmallFloatsApp extends SmallFloatsCore 
                              with SmallFloatsCodec
                              with SmallFloatsReconstructor
                              with SmallFloatsRefinementStrategy {
}

object FxPntSmallFloatsApp extends SmallFloatsCore 
                              with SmallFloatsCodec
                              with FixpointReconstruction
                              with SmallFloatsRefinementStrategy {
}