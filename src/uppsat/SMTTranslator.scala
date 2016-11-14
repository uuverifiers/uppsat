package uppsat

import scala.collection.mutable.Set

class SMTTranslator(theory : Theory) {
  var definedSymbols = Set() : Set[ConcreteFunctionSymbol]
  
  def translateNode(node : Node) : String = {
     node match {
       case InternalNode(symbol, desc) => {
           val fun = symbol.theory.toSMTLib(symbol) 
           val args = desc.map(translateNode)
           "(" + fun + " " + args.mkString(" ") + ")"
       }
       case LeafNode(symbol) => {
         // TODO: Refine this...
         if (!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {
           definedSymbols += symbol 
         }
         symbol.theory.toSMTLib(symbol)
       }
     }
  }
  
  def declarations(symbols : List[ConcreteFunctionSymbol]) = {
    (for (s <- symbols) yield
      s.theory.declarationToSMTLib(s)).filter(_ != "").mkString("\n")
  }
  
  def translate(node : Node) : String = {
    definedSymbols = Set()
    val assertions = "(assert " + translateNode(node) + ")"

    header + "\n" +
    declarations(definedSymbols.toList) + "\n" +
    assertions + "\n" +
    footer
  }
  
  def header = {
    theory.SMTHeader
  }
  
  def footer = {
    "(check-sat)"
  }
  
  def getDefinedSymbols = definedSymbols.toSet
}