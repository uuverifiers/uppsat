package uppsat.parser

import uppsat.ast.Sort
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.ast.AST

import scala.collection.mutable.Map

// We should not be adding || afterwards?

class Environment {
  var symbols : Map[String, ConcreteFunctionSymbol] = Map()
  var definitions : Map[String, AST] = Map()
  var assumptions : List[AST] = List()

  def addSymbol(id : String, symbol : ConcreteFunctionSymbol) = {
    symbols += id -> symbol
  }
  
  def addDefinition(id : String, definition : AST) = {
    definitions += id -> definition
  }

  def addAssumption(ass : AST) = {
    assumptions = ass :: assumptions
  }
  
  def findSymbol(id : String) : Option[ConcreteFunctionSymbol] = {
    if (symbols contains id)
      Some(symbols(id))
    else
      None 
  }
  
  def findDefinition(id : String) : Option[AST] = {
    if (definitions contains id)
      Some(definitions(id))
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
