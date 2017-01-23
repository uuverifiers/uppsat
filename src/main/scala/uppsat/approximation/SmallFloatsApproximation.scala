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






object SmallFloatsApproximation extends TemplateApproximation {
  type P = Int
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  val precisionOrdering = new IntPrecisionOrdering(0, 5)
  
  val DEBUG = false
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    val topTen = 10 // K 
    val fractionToRefine = 0.3 //K_percentage
    val precisionIncrement = 1 // 20/100 = 1/5
    
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
    
    def nodeError(accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {
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

    val accu = Map[AST, Double]()
    val errorRatios = AST.postVisit(ast, accu, nodeError)
    
    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
    
    def boolCond( accu : List[AST], ast : AST, path : Path) : Boolean = {
      decodedModel(ast) != failedModel(ast)
    }
    
    def boolWork( accu : List[AST], ast : AST) : List[AST] = {      
      ast :: accu
    }
    
    
    val nodesToRefine = AST.boolVisit(ast, List(), boolCond, boolWork).toSet
    
    
    var newPMap = pmap
    var changes = 0
    println("Nodes to refine ")
    println(nodesToRefine.map(_.ppWithModels("", decodedModel, failedModel)).mkString("\n\n"))
    for (node <- nodesToRefine) { //.take(k)
      val p =  newPMap(node.label)
      val newP = (p + precisionIncrement) max p
      newPMap = newPMap.update(node.label , newP min pmap.precisionOrdering.max)
      if  ( p  != pmap.precisionOrdering.max) {
        changes += 1
      } else {
        println("Already at max precision " + node.label)
      }
    }
    
    if (changes == 0) {
      println(nodesToRefine)
      throw new Exception("Nothing changed in pmap")
    }
//    println("--------------------------------------\nNew precision map :")
//    println(newPMap)
    newPMap    
    //    pmap.map(_ + 1)
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
  
  def scaleSort(sort : FPSort, p : Int) = {
    val eBits = 3 + ((sort.eBits - 3) * p)/precisionOrdering.max
    val sBits = 3 + ((sort.sBits - 3) * p)/precisionOrdering.max
    sort.getFactory(List(eBits, sBits))
  }
  
  def cast(ast : AST, target : ConcreteSort  ) : AST = {
    val source = ast.symbol.sort
    if (ast.symbol.sort != RoundingModeSort && source != target ) {      
      val cast = FPToFPFactory(List(ast.symbol.sort, target))
      val rtzNode = AST(RoundToZero, List(), List())
      AST(cast, List(), List(rtzNode, ast))
    } else {
      ast
    } 
  }
  
  def encodeFunSymbol(symbol : FloatingPointFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
      val newSort = scaleSort(symbol.sort, precision)
      val newChildren = 
        if (symbol.getFactory == FPToFPFactory) {// No need to cast, this symbol does this!
          children
        } else {
          for ( c <- children) yield {
             cast(c, newSort)                   
          }
        }
      val argSorts = newChildren.map( _.symbol.sort)
      AST(symbol.getFactory(argSorts ++ List(newSort)), path, newChildren)
    }
  
    def compareSorts(s1 : Sort, s2 : Sort) = {
      (s1, s2) match {
        case (FPSort(eb1, sb1), FPSort(eb2, sb2)) => eb1 + sb1 > eb2 + sb2
        case (FPSort(_, _), _) | (_, FPSort(_, _)) => true        
      }
    }
    
    def encodePredSymbol(symbol : FloatingPointPredicateSymbol, path : Path, children : List[AST], precision : Int) : AST = {
      val newSort = children.tail.foldLeft(children.head.symbol.sort)((x,y) => if (compareSorts(x, y.symbol.sort)) x else  y.symbol.sort)
      val newChildren = 
        for ( c <- children) yield {
          cast(c, newSort)          
        }
      val argSorts = newChildren.map( _.symbol.sort)
      AST(symbol.getFactory(argSorts ++ List(symbol.sort)), path, newChildren)      
    }
    
    def encodeVar(fpVar : FPVar, path : Path, precision : Int) = {
      // TODO: Do not convert if sorts are the same
      val newSort = scaleSort(fpVar.sort, precision)
      val newVar = FPVar(fpVar.name)(newSort)
      uppsat.ast.Leaf(newVar, path)     
    }
    
   def encodeSymbol(ast : AST, children : List[AST], precision : Int) : AST = {
    ast.symbol match {
      case fpLit : FloatingPointConstantSymbol => {
        ast 
      }
      case fpSym : FloatingPointFunctionSymbol => {
        encodeFunSymbol(fpSym, ast.label, children, precision)
      }
      case fpPred : FloatingPointPredicateSymbol => {
        encodePredSymbol(fpPred, ast.label, children, precision)
      }
      case fpVar : FPVar => {
        encodeVar(fpVar, ast.label, precision)
      }
      case _ => {
        AST(ast.symbol, ast.label, children) 
      }
    }
   }
 
    
  def encodeAux(ast : AST, pmap : PrecisionMap[Int]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, pmap)
      }    
    encodeSymbol(ast, newChildren, pmap(ast.label))    
  }
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Int]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    encodeAux(ast, pmap)    
  }
  
  // DECODING
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : Int) = {
    (symbol.sort, value.symbol) match {
      case (FPSort(e, s), fp : FloatingPointTheory.FloatingPointLiteral)  => {
        val fullEBits = fp.eBits.head :: List.fill(e - fp.eBits.length)(0) ++ fp.eBits.tail
        // TODO: Should it be s-1...
        val fullSBits = fp.sBits ++ List.fill((s - 1) - fp.sBits.length)(0)
        Leaf(FPLiteral(fp.sign, fullEBits, fullSBits, FPSort(e, s)))
      }
      
      // TODO: We have to fix infinity and scale it ... all constants?
      // TODO:  Signed Zeroes?
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
  
  def decodeNode( args : (Model, PrecisionMap[P]), decodedModel : Model, ast : AST) : Model = {
    val appModel = args._1
    val pmap = args._2
    
    val decodedValue = decodeSymbolValue(ast.symbol, appModel(ast), pmap(ast.label))
    
    if (decodedModel.contains(ast)){
      if (decodedModel(ast).toString() != decodedValue.toString()) {
         ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + decodedModel(ast) + " \n" + decodedValue)
      }
    } else {
      decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }
  
  def getCurrentValue(ast : AST, decodedModel : Model, candidateModel : Model) : AST = {
    if (! candidateModel.contains(ast)) {
          candidateModel.set(ast, decodedModel(ast))
        } 
    candidateModel(ast)
  }
  

  
  //******************************************************************//
  //                    Equality as Assignment                        //
  //******************************************************************//
  def equalityAsAssignment(ast : AST, decodedModel : Model,  candidateModel : Model) : Boolean = {
    ast match {
      case AST(fpEq : FPEqualityFactory.FPPredicateSymbol, path, children) if (decodedModel(ast).symbol == BoolTrue)  => {
         val lhs = children(0)
         val rhs = children(1)         
         val lhsDefined = candidateModel.contains(lhs)
         val rhsDefined = candidateModel.contains(rhs) 
         (lhs, rhs) match {         
           case ( _ , _ ) if (lhs.isVariable && rhs.isVariable) => {
//             println("Both variables")
             (lhsDefined, rhsDefined) match {
               case (false, true) => candidateModel.set(lhs, candidateModel(rhs))
                                     true
               case (true, false) => candidateModel.set(rhs, candidateModel(lhs))
                                     true
               case (false, false) => //TODO: Fancy things could be done here.
                                      false
               case (true, true) => false
             }
           }           
           case ( _ , _ ) if (lhs.isVariable && !lhsDefined) => {
//             println("LHS is undef variable")
             candidateModel.set(lhs, candidateModel(rhs))
             true
           }
           case ( _ , _) if (rhs.isVariable && !rhsDefined) =>{
//             println("RHS is undef variable")
             candidateModel.set(rhs, candidateModel(lhs))
             true
           }
           case (_, _) => {
//             println("no variables")
             false
           }
        }
      }
      case _ => false
    }
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
  
  // TODO: Remove when SmallFloats extends Template Approximation
//  def reconstruct(ast : AST, decodedModel : Model) : Model = {
//    val reconstructedModel = new Model()    
//    AST.postVisit(ast, reconstructedModel, decodedModel, reconstructNode)
//    reconstructedModel
//  }
}