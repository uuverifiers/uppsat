package uppsat

import scala.collection.mutable.Map

class PrecisionMap[T] {
  
  val map = Map() : Map[Node, T]
  
  def update(node : Node, newP : T) = {
    map += (node -> newP) //TODO: Check for maximum precision
  }
  
  def apply(node : Node) = map(node) //TODO: getorelse
  
}