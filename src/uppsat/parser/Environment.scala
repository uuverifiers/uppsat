package uppsat.parser

import uppsat.ast.Sort
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.ast.AST

import scala.collection.mutable.Map

class Environment {
  var symbols : Map[String, ConcreteFunctionSymbol] = Map()
  var assumptions : List[AST] = List()

  def addSymbol(id : String, symbol : ConcreteFunctionSymbol) = {
    symbols += id -> symbol
  }

  def addAssumption(ass : AST) = {
    assumptions = ass :: assumptions
  }
  
  def find(id : String) : Option[ConcreteFunctionSymbol] = {
    if (symbols contains id)
      Some(symbols(id))
    else
      None 
  }

  def lookup(id : String) = {
    symbols.find(_._1 == id).get._2
  }

  def print = {
    println("myEnv:")
    for ((id, symbol) <- symbols) {
      println("\t" + id + ": " + symbol + " (" + symbol.sort + ")")
    }
    for (ass <- assumptions) {
      println("\tASSUMPTION: " + ass)
    }
  }
}
