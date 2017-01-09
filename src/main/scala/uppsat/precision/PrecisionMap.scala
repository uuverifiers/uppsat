package uppsat.precision

import PrecisionMap._
import uppsat.ast.AST
import uppsat.ast.Leaf

object PrecisionMap {
  type Path = List[Int]
  
  def apply[T](implicit precisionOrdering : PrecisionOrdering[T]) = new PrecisionMap[T](Map.empty[Path, T])
}

class PrecisionMap[T](private val map : Map[Path, T])(implicit val precisionOrdering : PrecisionOrdering[T]) {  
  
  def update(path : Path, newP : T) = {
    if (precisionOrdering.lt(precisionOrdering.max, newP))
        throw new Exception("Trying to set precision larger than maximum precision")
    else
      new PrecisionMap[T](map + (path -> newP))
  }
  
  //TODO: What do we need to make this work?
  //  def increment(path : Path, incr : T) = {
  //    val currentP = map(path)
  //    val newP = currentP + incr
  //    if (precisionOrdering.lt(precisionOrdering.max, newP))
  //        throw new Exception("Trying to set precision larger than maximum precision")
  //    else
  //      new PrecisionMap[T](map + (path -> newP))
  //  }
  
  def isMaximal = {
    map.values.find(x => precisionOrdering.lt(x, precisionOrdering.max)).isEmpty
  }
  
  def map(f : T => T) : PrecisionMap[T] = {
    new PrecisionMap[T](map.map(x => {
      val (k, v) = x
      (k, f(v))
      }))
  }
  
  def cascadingUpdate(prefix : Path, ast : AST, newPrecision : T) : PrecisionMap[T]= {
    ast match {
      case Leaf(_) => update(prefix, newPrecision)
      case AST(_, _, children) => {
         var pmap = this
         for ( i <- children.indices)
           pmap = pmap.cascadingUpdate(i :: prefix, children(i), newPrecision)
         pmap.update(prefix, newPrecision)
      }      
    }
  }
  
  // Takes the maximum precision of the two
  def merge(that : PrecisionMap[T]) = {
    val newMappings = for ((k, v) <- that.map if (!(this.map contains k) || (this.map(k).asInstanceOf[Int] < v.asInstanceOf[Int]))) yield (k -> v)
    new PrecisionMap[T](map ++ newMappings)
  }
  
  // TODO: Do we want a check here?
  def apply(path : Path) = map(path)
  
  override def toString() = {
    map.toList.map(x => x match { case (k, v) => k + " => " + v }).mkString("\n")
  }
  
}