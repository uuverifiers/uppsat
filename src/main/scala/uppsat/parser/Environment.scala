package uppsat.parser

import uppsat.ast._
import uppsat.theory.BooleanTheory._

import scala.collection.mutable.Map

// We should not be adding || afterwards?

class Environment {
  var symbols : Map[String, ConcreteFunctionSymbol] = Map()
  var definitions : Map[String, (ConcreteFunctionSymbol, AST)] = Map()
  var assumptions : List[AST] = List()

  def addSymbol(id : String, symbol : ConcreteFunctionSymbol) = {
    symbols += id -> symbol
  }
  
  def addDefinition(id : String, symbol : ConcreteFunctionSymbol, definition : AST) = {
    definitions += id -> (symbol, definition)
  }

  def addAssumption(ass : AST) = {
    if (assumptions.isEmpty) {
      assumptions = ass :: assumptions
      false
    } else {  
      true
    }
  }
  
  def findSymbol(id : String) : Option[ConcreteFunctionSymbol] = {
    if (symbols contains id)
      Some(symbols(id))
    else
      None 
  }
  
  def findDefinition(id : String) : Option[AST] = {
    if (definitions contains id)
      Some(Leaf(definitions(id)._1))
    else
      None 
  }  

  def lookup(id : String) = {
    symbols.find(_._1 == id).get._2
  }
  
  def getFormula = {
    val defAssertions = 
      (for ((name, (symbol, definition)) <- definitions) yield {
        (Leaf(symbol) === definition)
      }).toList
    
    AST(naryConjunction(assumptions.length + defAssertions.length), assumptions.toList ++ defAssertions)
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
