package uppsat

import scala.collection.mutable.MutableList

class SMTTranslator(theory : Theory) {
  var definedSymbols = MutableList() : MutableList[FunctionSymbol]
  
  def translateNode(node : Node) : String = {
     node match {
       case InternalNode(symbol, desc) => {
           val fun = theory.toSMTLib(symbol) 
           val args = desc.map(translateNode)
           "(" + fun + " " + args.mkString(" ") + ")"
       }
       case LeafNode(symbol) => {
         // TODO: Refine this...
         if (!(theory.symbols contains symbol)) {
           definedSymbols += symbol 
         }
         theory.toSMTLib(symbol)
       }
     }
  }
  
  def declarations(symbols : List[FunctionSymbol]) = {
    (for (s <- symbols) yield
      theory.declarationToSMTLib(s)).mkString("\n")
  }
  
  def translate(node : Node) : String = {
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
}