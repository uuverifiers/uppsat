package uppsat.parser

class Environment {
  var symbols : List[(String, String)] = List()
  var assumptions : List[String] = List()

  def addSymbol(symb : String, sort : String) = {
    symbols = (symb, sort) :: symbols
  }

  def addAssumption(ass : String) = {
    assumptions = ass :: assumptions
  }

  def lookup(id : String) = {
    symbols.find(_._1 == id).get._2
  }

  def print = {
    println("myEnv:")
    for ((sym, sort) <- symbols) {
      println("\tSYMBOL: " + sym + " (" + sort + ")")
    }
    for (ass <- assumptions) {
      println("\tASSUMPTION: " + ass)
    }
  }
}
