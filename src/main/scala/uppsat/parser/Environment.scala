package uppsat.parser

import scala.collection.mutable.{Stack, Map => MMap}

import uppsat.ast._
import uppsat.theory._
import uppsat.theory.BooleanTheory._

// We should not be adding || afterwards?

class Environment {
  var symbols : Map[String, ConcreteFunctionSymbol] = Map()
  var definitions : Map[String, (ConcreteFunctionSymbol, AST)] = Map()
  var assumptions : List[AST] = List()
  var info : Map[String, String] = Map()
  var result : uppsat.ApproximationSolver.Answer =
    uppsat.ApproximationSolver.Unknown
  var theory : Option[Theory] = None
  var theoryGuess : Option[Theory] = None

  var letBindings : Stack[Map[String, ConcreteFunctionSymbol]] = new Stack()
  var letEquations : List[AST] = List()
  var letSuffix : Int = 0


  def setTheory(t : Theory) = {
    theory = Some(t)
  }

  def addSymbol(id : String, symbol : ConcreteFunctionSymbol) = {
    symbols += id -> symbol
  }

  def addDefinition(id : String,
                    symbol : ConcreteFunctionSymbol,
                    definition : AST) = {
    definitions += id -> (symbol, definition)
  }

  def addInfo(key : String, value : String) ={
    info += key -> value
  }

  def getInfo() = {
    info
  }

  // Pushes the bindings and returns a list with new symbols that should be used
  def pushLet(bindings : List[(String, AST)]) = {
    val specialChars = "#:"
    val tmp =
      for ((name, ast) <- bindings) yield {
        // First strip any surrounding |
        val stripName =
          if (name.startsWith("|") && name.endsWith("|"))
            name.substring(1, name.length - 1)
          else
            name
        val letName = "let" + letSuffix + "_" + stripName
        val newVarName =
          if (name.exists(specialChars.contains(_)))
            "|" + letName + "|"
          else
            letName
        letSuffix += 1

        val newVar =
          ast.symbol.sort match {
            // TODO: (Peter) There should be some unified procedure for this
            case uppsat.theory.IntegerTheory.IntegerSort =>
              new uppsat.theory.IntegerTheory.IntVar(newVarName)
            case BooleanSort =>
              new uppsat.theory.BooleanTheory.BoolVar(newVarName)
            case fp : uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort =>
              new uppsat.theory.FloatingPointTheory.FPVar(newVarName, fp)
            case uppsat.theory.FloatingPointTheory.RoundingModeSort =>
              new uppsat.theory.FloatingPointTheory.RMVar(newVarName)
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

    AST(naryConjunction(assumptions.length + defAssertions.length +
                          letEquations.length),
        assumptions.toList ++ defAssertions ++ letEquations)
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
