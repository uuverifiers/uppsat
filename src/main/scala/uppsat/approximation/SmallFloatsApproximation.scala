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






object SmallFloatsApproximation extends Approximation {
  type P = Int
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  val precisionOrdering = new IntPrecisionOrdering(0, 5)
  
  def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
//    val topTen = 10 // K 
//    val fractionToRefine = 0.3 //K_percentage
//    val precisionIncrement = 1 // 20/100 = 1/5
//    
//    def relativeError(decoded : FloatingPointLiteral, precise : FloatingPointLiteral) : Double = {
//      (decoded.getFactory, precise.getFactory) match {
//        case (x, y) if (x == y) => 0.0 //Values are the same
//        case (FPPlusInfinity, _)    |
//             (_, FPPlusInfinity)    |
//             (FPMinusInfinity, _)   |
//             (_, FPMinusInfinity)   => Double.PositiveInfinity
//        case (x : FPConstantFactory, y : FPConstantFactory) => {
//          val a = bitsToDouble(decoded)
//          val b = bitsToDouble(precise)
//          Math.abs((a - b)/b)
//        }        
//        case _ => 0.0
//      }
//    }
//    
//    def nodeError(accu : Map[Path, Double], ast : AST, path : Path) : Map[Path, Double] = {
//      val AST(symbol, label, children) = ast
//      
//      var err = 0.0
//      
//      symbol match {
//        case literal : FloatingPointLiteral => ()
//        case fpfs : FloatingPointFunctionSymbol =>
//          (decodedModel(path).symbol, failedModel(path).symbol)  match {
//          case (app : FloatingPointLiteral, ex : FloatingPointLiteral) => {
//            val outErr = relativeError(app, ex)
//            
//            var sumDescError = 0.0
//            var numFPArgs = 0
//            
//            for ((c, i) <- children zip children.indices) {
//              val a = decodedModel(i :: path)
//              val b = failedModel(i :: path)
//              
//              (a.symbol, b.symbol) match {
//                case (aS : FloatingPointLiteral, bS: FloatingPointLiteral) => {
//                  sumDescError +=  relativeError(aS, bS)
//                  numFPArgs += 1
//                }                                                                 
//                case  _ => ()
//              }
//            }
//            val inErr = sumDescError / numFPArgs
//            
//            if (numFPArgs == 0) 
//              err = outErr
//            else
//              err = outErr / inErr
//          }
//          case _ => ()
//        }
//        case _ => ()
//      }
//      
//      
//      if (err == 0.0)
//        accu
//      else
//        accu + (path -> err)
//    }
//
//    val accu = Map[Path, Double]()
//    val errorRatios = AST.postVisit(ast, List(0), accu, nodeError)
//    
//    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
//    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
//    
//    def boolCond( accu : List[Path], ast : AST, path : Path) : Boolean = {
//      println("Path : " + path)
//      println("App model : " + decodedModel(path))
//      println("Failed model : " + failedModel(path))
//      println(decodedModel(path) != failedModel(path))
//      decodedModel(path) != failedModel(path)
//    }
//    
//    def boolWork( accu : List[Path], ast : AST, path : Path) : List[Path] = {
//      path :: accu
//    }
//    
//    
//    val pathsToRefine = AST.boolVisit(ast, List(0), List(), boolCond, boolWork) 
//    
//    
//    var newPMap = pmap
//    var changed = false
//    println(pathsToRefine.mkString("\n"))
//    for (path <- pathsToRefine) { //.take(k)
//      val p = pmap(path)
//      val newP = p + precisionIncrement
//      if  ( p  != pmap.precisionOrdering.max) {
//        changed = true
//        if (newP < pmap.precisionOrdering.max)
//          newPMap = newPMap.update(path, newP)
//        else  
//          newPMap = newPMap.update(path, pmap.precisionOrdering.max)
//      }        
//    }
//    
//    if (!changed) {
//      println(pathsToRefine)
//      throw new Exception("Nothing changed in pmap")
//    }
//    println("--------------------------------------\nNew precision map :")
//    println(newPMap)
//    newPMap    
        pmap.map(_ + 1)
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
  
  def scaleSort(sort : FPSort, p : Int) = {
    val eBits = 3 + ((sort.eBits - 3) * p)/precisionOrdering.max
    val sBits = 3 + ((sort.sBits - 3) * p)/precisionOrdering.max
    sort.getFactory(List(eBits, sBits))
  }
  
  
    def encodeFunSymbol(symbol : FloatingPointFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
      val newSort = scaleSort(symbol.sort, precision)
      val newChildren = 
        if (symbol.getFactory == FPToFPFactory) {
          // No need to cast, this symbol does this!
          children
        } else {
          for ( c <- children) yield {
            if (c.symbol.sort != RoundingModeSort && c.symbol.sort != newSort ) {
              val cast = FPToFPFactory(List(c.symbol.sort, newSort))
              AST(cast, List(), List(AST(RoundToZero, List(), List()), c))
            } else {
              c
            }          
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
          if (c.symbol.sort != newSort) {
            val cast = FPToFPFactory(List(c.symbol.sort, newSort))
            AST(cast, List(), List(AST(RoundToZero, List(), List()), c))
          } else {
            c
          }          
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
    
   def encodeSymbol(symbol : ConcreteFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
    symbol match {
      case fpLit : FloatingPointConstantSymbol => {
        AST(symbol, path, children) 
      }
      case fpSym : FloatingPointFunctionSymbol => {
        encodeFunSymbol(fpSym, path, children, precision)
      }
      case fpPred : FloatingPointPredicateSymbol => {
        encodePredSymbol(fpPred, path, children, precision)
      }
      case fpVar : FPVar => {
        encodeVar(fpVar, path, precision)
      }
      case _ => {
        AST(symbol, path, children) 
      }
    }
   }
 
    
  def encodeAux(ast : AST, path : Path, pmap : PrecisionMap[Int]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, i :: path, pmap)
      }    
    encodeSymbol(symbol, path, newChildren, pmap(path))    
  }
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Int]) : AST = Timer.measure("SmallFloats.encodeFormula") {
    encodeAux(ast, List(0), pmap)
  }
  
  
  
  // DECODING
  
  // TODO: _Symbol should have a sort?
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
  
  def decodeAux(ast : AST, path : Path, appModel : Model, decodedModel : Model, pmap : PrecisionMap[Int]) : Unit = {
    val AST(symbol, label, children) = ast
    
    
    val partialModels = 
      for ((c, i) <- children zip children.indices) yield {
        decodeAux( c, i :: path, appModel, decodedModel, pmap)
      }    
    
    
    val decodedValue = decodeSymbolValue(symbol, appModel(ast), pmap(path))
    
    if (decodedModel.contains(ast)){
      if (decodedModel(ast).toString() != decodedValue.toString()) {
         ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + decodedModel(ast) + " \n" + decodedValue)
      }
    } else {
      decodedModel.set(ast, decodedValue)
    }
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    val decodedModel = new Model()
    decodeAux(ast, List(0), appModel, decodedModel, pmap)
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
         (lhs.symbol, rhs.symbol) match {         
           case ( _ : FPVar, _ : FPVar) => {
             println("Both variables")
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
           case ( _ : FPVar, _ ) if (!lhsDefined) => {
//             println("LHS is undef variable")
             candidateModel.set(lhs, candidateModel(rhs))
             true
           }
           case ( _ , v1 : FPVar) if (!rhsDefined) =>{
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

  
  def reconstructNode(ast : AST, path : Path, decodedModel : Model, candidateModel : Model) : Unit = {
    val AST(symbol, label, children) = ast
    
    val Z3online = new Z3OnlineSolver()

    
    if (!equalityAsAssignment(ast, decodedModel, candidateModel) && children.length > 0) {
      val newChildren = for ( c <- children) yield {        
        getCurrentValue(c, decodedModel, candidateModel)
      }
      
      
      
      //Evaluation
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelReconstructor.evalAST(newAST, FloatingPointTheory)
      if (symbol.sort == BooleanTheory.BooleanSort) {
        val assignments = candidateModel.getAssignmentsFor(ast).toList
        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
        
        val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
        if ( backupAnswer != answer )
          throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)

      }        
      candidateModel.set(ast, newValue)
    }
  }
  
  def reconstructAux(ast : AST, path : Path, decodedModel : Model, candidateModel : Model) : Unit= {
    val AST(symbol, label, children) = ast
    for ((c, i) <- children zip children.indices) {
      reconstructAux( c, i :: path, decodedModel, candidateModel)
    } 
    reconstructNode(ast, path, decodedModel, candidateModel)
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    val reconstructedModel = new Model()
    reconstructAux(ast, List(0), decodedModel, reconstructedModel)
    reconstructedModel
  }
}