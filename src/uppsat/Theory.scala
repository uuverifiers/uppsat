package uppsat

trait Theory {
    // Sort
    // Symbol, consts, funs, variables
  
    val name : String
    val sorts : Seq[Sort]
    val symbols : Seq[FunctionSymbol]
    
    
    def SMTHeader : String
    def toSMTLib(symbol : FunctionSymbol) : String
    def toSMTLib(sort : Sort) : String
    def declarationToSMTLib(symbol : FunctionSymbol) : String
}