package uppsat

object PrecisionMap {
  type Path = List[Int]
  
  def apply[T]() = new PrecisionMap[T](Map.empty[Path, T])
}

import PrecisionMap._

// TODO: make map private
class PrecisionMap[T](val map : Map[Path, T]) {  
  
  def update(path : Path, newP : T) = {
    new PrecisionMap[T](map + (path -> newP)) //TODO: Check for maximum precision
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
    // TODO: Make T ordered
    val newMappings = for ((k, v) <- that.map if (!(this.map contains k) || (this.map(k).asInstanceOf[Int] < v.asInstanceOf[Int]))) yield (k -> v)
    new PrecisionMap[T](map ++ newMappings)
  }
  
  def apply(path : Path) = map(path) //TODO: getorelse
  
  override def toString() = {
    map.toList.map(x => x match { case (k, v) => k + " => " + v }).mkString("\n")
  }
  
}