package uppsat.precision

import PrecisionMap._
import uppsat.ast.AST
import uppsat.ast.Leaf
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.globalOptions.verbose
import uppsat.globalOptions

/** Mapping nodes in an AST to precisions.
  *
  * The map connects paths of nodes in an AST to precisions.
  */
object PrecisionMap {
  type Path = List[Int]

  /** Creates a precision map based on formula
    *
    * Creates a new precision map based on the formula given. It computes the
    * representative.
    */
  def apply[T](formula : AST)(implicit pOrd : PrecisionOrdering[T]) = {

    def collectPathVarPairs (a : Map[Path, ConcreteFunctionSymbol], ast : AST)
        : Map[Path, ConcreteFunctionSymbol] = {
      if (ast.isVariable)
          a + (ast.label -> ast.symbol)
      else
          a
    }

    val pathsToVar = AST.postVisit(formula,
                                   Map[Path, ConcreteFunctionSymbol](),
                                   collectPathVarPairs)
    val varToPaths = pathsToVar.groupBy(_._2).mapValues(_.keySet)
    val allPaths = formula.iterator.map { x => x.label }
    val representativeIterator = for (path <- allPaths) yield {
      if (pathsToVar.contains(path)) {
        val variable = pathsToVar(path)

        if (!varToPaths.contains(variable)) {
          val msg =
            "Precision map's variable to path consistency is compromised"
          throw new Exception(msg)
        }

        (path, varToPaths(variable).head)
      } else
        (path,  path)
    }
    implicit val representative = representativeIterator.toMap[Path, Path]

   new PrecisionMap[T](Map.empty[Path, T])
  }
}


/** Mapping nodes in an AST to precisions.
  *
  * The map connects paths of nodes in an AST to precisions.
  */
class PrecisionMap[T] private (val map : Map[Path, T])
                              (implicit val representative : Map[Path, Path],
                               val pOrd : PrecisionOrdering[T]) {

  /** Helpful debug output */
  def characterize = {
    if (globalOptions.VERBOSE) {
      var s = pOrd.minimalPrecision
      for ( v <- map.values) {
        s = pOrd.+(s, v)
      }
      verbose("#" + s)
    }
  }

  /** Update a precision of the map.
    *
    * @param path Path to node to be updated
    * @param newP New precision
    */
  def update(path : Path, newP : T) = {
    if (pOrd.lt(pOrd.maximalPrecision, newP)) {
      val msg = "Trying to set precision larger than maximum precision"
      throw new Exception(msg)
    } else {
      new PrecisionMap[T](map + (representative(path) -> newP))
    }
  }

  // TODO: What do we need to make this work?
  //  def increment(path : Path, incr : T) = {
  //    val currentP = map(path)
  //    val newP = currentP + incr
  //    if (pOrd.lt(pOrd.max, newP))
  //        throw new Exception("Trying to set precision
  //         larger than maximum precision")
  //    else
  //      new PrecisionMap[T](map + (path -> newP))
  //  }

  /** Checks if all precisions in map are maxiaml */
  def isMaximal = {
    map.values.find(x => pOrd.lt(x, pOrd.maximalPrecision)).isEmpty
  }

  /** A precision map with all nodes set to maximal precision */
  def maximal = {
    new PrecisionMap(map.map{ case (k, v) => (k, pOrd.maximalPrecision)})
  }


  /** Map function, i.e., perform function on each node */
  def map(f : T => T) : PrecisionMap[T] = {
    new PrecisionMap[T](map.map(x => {
      val (k, v) = x
      (k, pOrd.min(f(v), pOrd.maximalPrecision))
      }))
  }

  /** Updates each node in {@code ast} with {@code newPrecision}. */
  def cascadingUpdate(ast : AST, newPrecision : T) : PrecisionMap[T]= {
    ast match {
      case Leaf(_) => update(ast.label, newPrecision)
      case AST(_, _, children) => {
        var pmap = this
        for (c <- children)
          pmap = pmap.cascadingUpdate(c, newPrecision)
         pmap.update(ast.label, newPrecision)
      }
    }
  }

  /** Merge two precision maps.
    *
    * Merges with precision map {@code that} by taking the maximum for each node
    * which overlaps.
    */
  def merge(that : PrecisionMap[T]) = {
    val newMappings =
      for ((k, v) <- that.map
          if (!(this.map contains k)
              || (this.pOrd.lt(this.map(k), v))))
        yield (k -> v)
    new PrecisionMap[T](map ++ newMappings)
  }

  /** Precision of node {@code path}. */
  def apply(path : Path) : T = {
      map(representative(path))
  }

  override def toString() = {
    map.toList.map(x => x match {
                     case (k, v) => k + " => " + v
                   }).mkString("\n")
  }
}
