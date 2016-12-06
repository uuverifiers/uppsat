package uppsat

import uppsat.theory.FloatingPointTheory._

import uppsat.ModelReconstructor.Model
import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.IntPrecisionOrdering
import uppsat.precision.PrecisionMap
import uppsat.theory.FloatingPointTheory
import uppsat.approximation.Approximation
import ast.AST
import ast.ConcreteFunctionSymbol
import ast.Sort


object SmallFloatsApproximation extends Approximation[Int] {
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  val precisionOrdering = new IntPrecisionOrdering(10)
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
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
        for ( c <- children) yield {
          if (c.symbol.sort != RoundingModeSort && c.symbol.sort != newSort ) {
            val cast = FPToFPFactory(List(c.symbol.sort, newSort))
            AST(cast, List(), List(AST(RoundToZero, List(), List()), c))
          } else {
            c
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
    
   def encodeSymbol(symbol : ConcreteFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
    symbol match {
      case fpLit : FloatingPointConstantSymbol => AST(symbol, path, children) 
      case fpSym : FloatingPointFunctionSymbol => encodeFunSymbol(fpSym, path, children, precision)
      case fpPred : FloatingPointPredicateSymbol => encodePredSymbol(fpPred, path, children, precision)
      case _ => AST(symbol, path, children) 
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
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Int]) : AST = {
    encodeAux(ast, List(0), pmap)
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    appModel
  }
  def reconstruct(ast : AST, decodedModel : Model) : Model = {
    decodedModel
  }
}