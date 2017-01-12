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
import uppsat.theory.BooleanTheory.BoolTrue
import uppsat.theory.BooleanTheory.BoolFalse
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory.BooleanFunctionSymbol
import uppsat.theory.BooleanTheory.BooleanConstant







object SmallFloatsApproximation extends Approximation {
  type P = Int
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  val precisionOrdering = new IntPrecisionOrdering(0, 5)
  
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
    
    def nodeError(accu : Map[Path, Double], ast : AST, path : Path) : Map[Path, Double] = {
      val AST(symbol, label, children) = ast
      
      var err = 0.0
      
      symbol match {
        case literal : FloatingPointLiteral => ()
        case fpfs : FloatingPointFunctionSymbol =>
          (decodedModel(path).symbol, failedModel(path).symbol)  match {
          case (app : FloatingPointLiteral, ex : FloatingPointLiteral) => {
            val outErr = relativeError(app, ex)
            
            var sumDescError = 0.0
            var numFPArgs = 0
            
            for ((c, i) <- children zip children.indices) {
              val a = decodedModel(i :: path)
              val b = failedModel(i :: path)
              
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
        accu + (path -> err)
    }

    val accu = Map[Path, Double]()
    val errorRatios = AST.postVisit(ast, List(0), accu, nodeError)
    
    val sortedErrRatios = errorRatios.toList.sortWith((x,y) => x._2 > y._2)
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions
    
    def boolCond( accu : List[Path], ast : AST, path : Path) : Boolean = {
      println("Path : " + path)
      println("App model : " + decodedModel(path))
      println("Failed model : " + failedModel(path))
      println(decodedModel(path) != failedModel(path))
      decodedModel(path) != failedModel(path)
    }
    
    def boolWork( accu : List[Path], ast : AST, path : Path) : List[Path] = {
      path :: accu
    }
    
    
    val pathsToRefine = AST.boolVisit(ast, List(0), List(), boolCond, boolWork) 
    
    
    var newPMap = pmap
    var changed = false
    println(pathsToRefine.mkString("\n"))
    for (path <- pathsToRefine) { //.take(k)
      val p = pmap(path)
      val newP = p + precisionIncrement
      if  ( p  != pmap.precisionOrdering.max) {
        changed = true
        if (newP < pmap.precisionOrdering.max)
          newPMap = newPMap.update(path, newP)
        else  
          newPMap = newPMap.update(path, pmap.precisionOrdering.max)
      }        
    }
    
    if (!changed) {
      println(pathsToRefine)
      throw new Exception("Nothing changed in pmap")
    }
    println("--------------------------------------\nNew precision map :")
    println(newPMap)
    newPMap    
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
  
  def decodeAux(ast : AST, path : Path, appModel : Model, pmap : PrecisionMap[Int]) : Model = {
    val AST(symbol, label, children) = ast
    val partialModels = 
      for ((c, i) <- children zip children.indices) yield {
        decodeAux( c, i :: path, appModel, pmap)
      }    
    
    // TODO: Literals have no children
    if (!isLiteral(symbol)) {
      val currentModel = Map(path -> decodeSymbolValue(symbol, appModel(path), pmap(path)))
      partialModels.foldLeft(currentModel)((x,y) => x ++ y)
    } else {
      Map()      
    }
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    decodeAux(ast, List(0), appModel, pmap)
  }
  
  def getCurrentValue(ast : AST, path : Path, decodedModel : Model, candidateModel : Model) : (AST, Model) = {
    if (isLiteral(ast.symbol)) {
      (ast, candidateModel)
    } else if (candidateModel.contains(path)) {
      (candidateModel(path), candidateModel)
    } else {
      //TODO: assert ast is variable
      (decodedModel(path), candidateModel + (path -> decodedModel(path))) 
    }
  }
  
  def reconstructNode(ast : AST, path : Path, decodedModel : Model, candidateModel : Model) : Model = {
    val AST(symbol, label, children) = ast
    
    var currModel = 
      (symbol, decodedModel.getOrElse(path, Leaf(BoolFalse)).symbol) match {
        case (fpEq : FPEqualityFactory.FPPredicateSymbol, BoolTrue) => {
         val v0Path = 0::path
         val v1Path = 1::path
         val v0Defined = candidateModel.contains(v0Path)
         val v1Defined = candidateModel.contains(v1Path)
         (children(0).symbol, children(1).symbol) match {         
           case ( v0 : FPVar, v1 : FPVar) => {
             (v0Defined, v1Defined) match {
               case (false, true) => candidateModel + (v0Path -> candidateModel(v1Path))
               case (true, false) => candidateModel + (v1Path -> candidateModel(v0Path))
               case (false, false) => candidateModel + (v1Path -> decodedModel(v0Path)) + (v0Path -> decodedModel(v0Path)) //TODO: Fancy things could be done here.
               case (true, true) => candidateModel
             }
           }           
           case ( v0 : FPVar, _ ) if (!v0Defined) => { 
             val (newC, newM) = getCurrentValue(children(1), v1Path, decodedModel, candidateModel)
             newM + (v0Path -> newC )
           }
           case ( _ , v1 : FPVar) if (!v1Defined) =>{
             val (newC, newM) = getCurrentValue(children(0), v0Path, decodedModel, candidateModel)
             newM + (v1Path -> newC )           
           }
           case (_, _) => candidateModel
        }
      }
      case _ => candidateModel     
      
    }
    
    val newChildren = for ( i <- 0 until children.length) yield { 
      val (newC, newM) = getCurrentValue(children(i), i :: path, decodedModel, currModel)
      currModel = newM
      newC
    }
    
    //TODO: Make this check more comprehensive
    if (children.length > 0) {
      val newAST = AST(symbol, label, newChildren.toList)
      val newValue = ModelReconstructor.evalAST(newAST, FloatingPointTheory, Z3Solver)
      if (newValue != decodedModel(path))
          println("::" + path + " " + decodedModel(path).prettyPrint("") + " / " + newValue.prettyPrint(""))
          
      if (symbol.sort == BooleanTheory.BooleanSort) {
        val assignments = for ((symbol, label) <- ast.subIterator(path) if (!symbol.theory.isDefinedLiteral(symbol))) yield {
          val value = currModel(label)
          (symbol.toString(), value.symbol.theory.toSMTLib(value.symbol) )
        }
  
        val backupAnswer = ModelReconstructor.valAST(ast, assignments.toList, this.inputTheory, Z3Solver)
        
        val answer = newValue.symbol.asInstanceOf[BooleanConstant] == BoolTrue
        if ( backupAnswer != answer )
          throw new Exception("Backup validation failed : \nEval: " + answer + "\nvalAst: " + backupAnswer)

      }
          
      currModel + (path -> newValue)
    } else { 
      currModel
    }
  }
  
  def reconstructAux(ast : AST, path : Path, decodedModel : Model, candidateModel : Model) : Model = {
    val AST(symbol, label, children) = ast
    var currModel = candidateModel
   
    for ((c, i) <- children zip children.indices) 
      currModel = reconstructAux( c, i :: path, decodedModel, currModel)
    
    val res = reconstructNode(ast, path, decodedModel, currModel)
    res
  }
  
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
     reconstructAux(ast, List(0), decodedModel, Map())
  }
}