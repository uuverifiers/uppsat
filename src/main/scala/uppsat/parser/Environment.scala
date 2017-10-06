package uppsat.parser

import uppsat.ast._
import scala.collection.mutable.Stack
import uppsat.theory.BooleanTheory._
import uppsat.theory._

import scala.collection.mutable.{Map => MMap, MutableList}
import uppsat.theory._
// We should not be adding || afterwards?

class Environment {
  var symbols : Map[String, ConcreteFunctionSymbol] = Map()
  var definitions : Map[String, (ConcreteFunctionSymbol, AST)] = Map()
  var assumptions : List[AST] = List()
  var result : uppsat.ApproximationSolver.Answer = uppsat.ApproximationSolver.Unknown
  var theory : Option[Theory] = None
  
  var theoryGuess : Option[Theory] = None
  
  var letBindings : Stack[Map[String, ConcreteFunctionSymbol]] = new Stack()
  var letEquations : MutableList[AST] = MutableList()
  var letSuffix : Int = 0
  

  //var synonyms : Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol] = Map()
  
  def setTheory(t : Theory) = {
    theory = Some(t)
  }
  
  def addSymbol(id : String, symbol : ConcreteFunctionSymbol) = {
    symbols += id -> symbol
  }
  
  def addDefinition(id : String, symbol : ConcreteFunctionSymbol, definition : AST) = {
    definitions += id -> (symbol, definition)
  }
  
  // Pushes the bindings and returns a list with new symbols that should be used
  def pushLet(bindings : List[(String, AST)]) = {
    val tmp = 
      for ((name, ast) <- bindings) yield {
        val newVarName = "let" + letSuffix + "_" + name
        letSuffix += 1
        
        val newVar = 
          ast.symbol.sort match {
            // TODO: (Peter) There should be some unified procedure for this
            case uppsat.theory.IntegerTheory.IntegerSort => new uppsat.theory.IntegerTheory.IntVar(newVarName)
            case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(newVarName)
            case fp : uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort => new uppsat.theory.FloatingPointTheory.FPVar(newVarName, fp)
            case uppsat.theory.FloatingPointTheory.RoundingModeSort => new uppsat.theory.FloatingPointTheory.RMVar(newVarName)
         }
        (name, ast, newVar)      
      }
    val newBindings = tmp.map(t => (t._1, t._3)).toMap
    letBindings.push(newBindings)
    
    val newEquations = tmp.map(t => t._2 === Leaf(t._3))
    letEquations = letEquations ++ (newEquations)
  }
  
  def popLet() = {
    letBindings.pop()
  }
  
  // TODO: (Peter) There is probably a more proper way of doing this
  def letContains(name : String) : Option[ConcreteFunctionSymbol] = {
    for (stack <- letBindings) {
      if (stack contains name) {
        return Some(stack(name))
      }
    }
    None
  }
  
  //  def addSynonym( alias : ConcreteFunctionSymbol, original : ConcreteFunctionSymbol) = {
  //    synonyms += alias -> original
  //  }

  def addAssumption(ass : AST) = {
    assumptions = ass :: assumptions
  }
  
  
  
  def findSymbol(id : String) : Option[ConcreteFunctionSymbol] = {
    if (symbols contains id) {
      Some(symbols(id))
    } else {
      letContains(id) 
    }
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
    
    AST(naryConjunction(assumptions.length + defAssertions.length + letEquations.length), assumptions.toList ++ defAssertions ++ letEquations)
  }

  def print = {
    println("myEnv:")
    for ((id, symbol) <- symbols) {
      println("\t" + id + ": " + symbol + " (" + symbol.sort + ")")
    }
    for (ass <- assumptions) {
      println("\tASSUMPTION: " + ass)
    }
    
    for ((name, (symbol, definition)) <- definitions) yield {
       println("\tDEFINITION: " + symbol + " : " + definition)
    }
    
    for (letStack <- letBindings) {
      println("LETSTACK: ")
      println(letStack.mkString("\n"))
    }
    
    for (le <- letEquations) {
      println("LET-EQUATION: " + le)
    }
      
  }
}
