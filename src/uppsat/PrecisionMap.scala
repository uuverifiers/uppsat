package uppsat

object PrecisionMap {
  def apply[T]() = new PrecisionMap[T](Map.empty[Node, T])
}

// TODO: make map private
class PrecisionMap[T](val map : Map[Node, T]) {

    
  def update(node : Node, newP : T) = {
    new PrecisionMap[T](map + (node -> newP)) //TODO: Check for maximum precision
  }
  
  // Takes the maximum precision of the two
  def merge(that : PrecisionMap[T]) = {
    // TODO: Make T ordered
    val newMappings = for ((k, v) <- that.map if (!(this.map contains k) || (this.map(k).asInstanceOf[Int] < v.asInstanceOf[Int]))) yield (k -> v)
    new PrecisionMap[T](map ++ newMappings)
  }
  
  def apply(node : Node) = map(node) //TODO: getorelse
  
  override def toString() = {
    map.toList.map(x => x match { case (k, v) => k + " => " + v }).mkString("\n")
  }
  
}