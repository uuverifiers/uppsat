package uppsat;

object main {
  def boolean() = {
    import uppsat.BooleanTheory._

    val a = new BoolVar("a")
    val b = new BoolVar("b")
    val c = new BoolVar("c")
    val t = BoolTrue

    val f = a & (!b & (t & (!c)))
    val translator = new SMTTranslator(BooleanTheory)
    val SMT = translator.translate(f)
    println(SMT)
  }

  def integer() = {
    import uppsat.IntegerTheory._
    import uppsat.BooleanTheory._

    val x = new IntVar("x")
    val y = new IntVar("y")

    ((x === (y - 4)) & ((x + y) === 6), List(x, y))

  }
  
  def main(args: Array[String]) = {
    val (formula, vars) = integer()
    println("<<<Formula>>>")
    formula.prettyPrint
    val enc = new Encoder[Int](IntApproximation)
    var pmap = PrecisionMap[Int]()

    pmap = pmap.cascadingUpdate(List(), formula, 1)

    val translator = new SMTTranslator(IntegerTheory)
    // TODO: How do we solve this logistically

    def tryZ3() = {

      import uppsat.PrecisionMap.Path
      import uppsat.Encoder.PathMap
      import uppsat.ModelReconstructor.Model

      var iterations = 0

      var finalModel = None: Option[Model]
      var sourceToEncoding = Map(): PathMap
      var haveAnAnswer = false
      var pFormula = formula
      var pSMT = ""

      while (!haveAnAnswer && iterations < 10) {
        var haveApproxModel = false

        // TODO: fix maximal pmap
        while (!haveApproxModel && iterations < 10) {
          iterations += 1
          println("Starting iteration " + iterations)
          
          val (newpFormula, newASTMap) = enc.encode(formula, pmap)
          pFormula = newpFormula
          sourceToEncoding = newASTMap
          pSMT = translator.translate(pFormula)

          val result = Z3Solver.solve(pSMT)

          if (result) {
            haveApproxModel = true
          } else {
            println("No approximative model found> updating precisions")
            // TODO: Unsat core reasoning
            pmap = IntApproximation.unsatRefine(formula, List(), pmap)
          }
        }

        if (haveApproxModel) {
          val model = Z3Solver.getModel(pSMT, translator.getDefinedSymbols.toList)
          val nodeModel = translator.getASTModel(pFormula, model)
          val reconstructor = new ModelReconstructor[Int](IntApproximation)
          val exactModel = reconstructor.reconstruct(formula, nodeModel, sourceToEncoding, pmap)

          def createGroundASTaux(ast : AST, path : Path, exactModel : Model) : AST = {
            ast match {
              case Leaf(symbol) => exactModel(path)
              case AST(symbol, children) => {
                val newChildren = 
                  for ((c, i) <- children zip children.indices) yield createGroundASTaux(c, i::path, exactModel)
                  AST(symbol, newChildren)
              }
            }
          }
          
          def groundAST(ast : AST, exactModel : Model) = {
            createGroundASTaux(ast, List(), exactModel)
          }
          
          def valAST(ast: AST, exactModel: Model): Boolean = {
            // Which approximate ast does the original ast correspond to?
            // sourceToEncoding has the answer

            //val exactDescValues = ast.children.indices.map(x => exactModel(List(x))).toList
            //val newAST = AST(ast.symbol, exactDescValues)
            val newAST = groundAST(ast, exactModel)
            val translator = new SMTTranslator(IntApproximation.outputTheory)
            val astSMT = translator.translateNoAssert(newAST)
            val result = Z3Solver.solve(astSMT)
            val smtModel = Z3Solver.getModel(astSMT, translator.getDefinedSymbols.toList)
            val astModel = translator.getASTModel(newAST, smtModel)
            val exactValue = astModel(List())
           
            exactValue.symbol match {
              case BooleanTheory.BoolFalse => false
              case BooleanTheory.BoolTrue  => true
            }
          }

          if (valAST(formula, exactModel)) {
            haveAnAnswer = true
            finalModel = Some(exactModel)
          } else {
            println("Model reconstruction failed> updating precisions")
            val newPmap = IntApproximation.satRefine(formula, nodeModel, exactModel, pmap)
            pmap = pmap.merge(newPmap)
          }
        }
      }

      if (haveAnAnswer == true) {
        println("Found model")
        
        def extractVariables(ast : AST, vars : List[ConcreteFunctionSymbol], model : Model) = {
          def eV(ast : AST, path : Path, vars : List[ConcreteFunctionSymbol]) : List[(ConcreteFunctionSymbol, AST)] = {
            if (vars.isEmpty) {
              List()
            } else {
              val AST(symbol, children) = ast
              val recursive = 
                (for ((c, i) <- children zip children.indices) yield {
                  eV(c, i :: path, vars)
                }).flatten
              if (vars contains symbol) {
                val newMapping = (symbol -> model(path))
                newMapping :: recursive
              } else {
                recursive
              }
            }
          }
          eV(ast, List(), vars).toSet.toMap
        }
        
        for ((k, v) <- extractVariables(formula, vars, finalModel.get)) {
          println(k + "\t" + v + "\t (" + v.getClass + ")")          
        }
        //          for (v <- vars)

      } else {
        println("No model found...")
      }
    }

    tryZ3()
  }
}
