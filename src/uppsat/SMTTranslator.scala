package uppsat

import scala.collection.mutable.{Set, Map, MutableList}

class SMTTranslator(theory : Theory) {
  //var definedSymbols = Set() : Set[ConcreteFunctionSymbol]
  
  // TODO: HACK
  //val symbolToNode = Map() : Map[ConcreteFunctionSymbol, Node]
  var nextNode = 0
  val nodeToId = Map() : Map[Node, String]
  val IdToNode = Map() : Map[String, Node]
  val nodeSymbols = Set() : Set[(String, String)]
  val symbolAssertions = MutableList() : MutableList[String]
  
  def translateNode(node : Node) : String = {
     // TODO: Make this proper?  
     node match {
       case InternalNode(symbol, desc) => {
           val fun = symbol.theory.toSMTLib(symbol) 
           val args = desc.map(translateNode)
           val thisNode = "(" + fun + " " + args.mkString(" ") + ")"
           
           // Create extra-symbol that contains the value of this node
           val nodeId = node.symbol.toString + nextNode.toString
           nodeToId += node -> nodeId
           IdToNode += nodeId -> node
           nextNode += 1             
           
           val newSymbol = nodeId
           val newSort  = symbol.sort.theory.toSMTLib(symbol.sort)
           val symbolAssertion = "(= " + newSymbol + " " + thisNode + ")" 
           nodeSymbols += ((newSymbol, newSort))
           symbolAssertions += symbolAssertion
           
           thisNode
       }
       case LeafNode(symbol) => {
         // TODO: Refine this...
         val thisNode = symbol.theory.toSMTLib(symbol)
         if (!BooleanTheory.isDefinedLiteral(symbol) || !theory.isDefinedLiteral(symbol)) {           
           val nodeId = thisNode
           nodeToId += node -> nodeId
           IdToNode += nodeId -> node
           
           val newSymbol = thisNode
           val newSort  = symbol.sort.theory.toSMTLib(symbol.sort)
           val symbolAssertion = "(= " + newSymbol + " " + thisNode + ")"    
           nodeSymbols += ((newSymbol, newSort))           
         }
         thisNode
       }
     }
  }
  
  def declarations(symbols : List[ConcreteFunctionSymbol]) = {
    (for (s <- symbols) yield
      s.theory.declarationToSMTLib(s)).filter(_ != "").mkString("\n")
  }
  
  def symDecs= {
    nodeSymbols.toList.map(x => x match { case (sym, sort) => "(declare-fun " + sym + " () " + sort + ")"}).mkString("\n")
  }
  
  def symAsserts= {
    symbolAssertions.map("(assert " + _ + ")").mkString("\n")
  }
  
  def translate(node : Node) : String = {
//    definedSymbols.clear()
    nextNode = 0
    nodeToId.clear()
//    symbolToNode.clear()
    nodeSymbols.clear()
    symbolAssertions.clear()
    
    val assertions = "(assert " + translateNode(node) + ")"
    
    header + "\n" +
//    declarations(definedSymbols.toList) + "\n" +
    symDecs + "\n" +
    symAsserts + "\n" + 
    assertions + "\n" +
    footer
  }
  
// TODO: What is a meaningful way to do this (sometimes we want to assert root node, sometimes don't)  
def translateNoAssert(node : Node) : String = {
//    definedSymbols.clear()
    nextNode = 0
    nodeToId.clear()
//    symbolToNode.clear()
    nodeSymbols.clear()
    symbolAssertions.clear()
    
   val assertions = "(assert " + translateNode(node) + ")"

    
    header + "\n" +
//    declarations(definedSymbols.toList) + "\n" +
    symDecs + "\n" +
    symAsserts + "\n" + 
    footer
  }  
  
  def header = {
    theory.SMTHeader
  }
  
  def footer = {
    "(check-sat)"
  }
  
  //    def getDefinedSymbols = definedSymbols.toSet ++ nodeSymbols.map(_._1)
  def getDefinedSymbols = nodeSymbols.map(_._1)  

  // TODO: Change ...mutable.Map to MMap
  def getNodeModel(model : scala.collection.immutable.Map[String, String]) : scala.collection.immutable.Map[Node, Node] = {
    (for ((k, v) <- model) yield {
      val node = IdToNode(k)
      val valNode = node.symbol.sort.theory.parseLiteral(v.trim()) //AZ: Should the trim call go elsewhere?
      node -> valNode
    }).toMap
  }
}