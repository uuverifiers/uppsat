//package uppsat.parser
//
//import uppsat.ast._
//import uppsat.theory.IntegerTheory.IntegerSort
//import uppsat.theory.BooleanTheory.BooleanSort
//import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
//import smtlib.parser.Terms._
//import uppsat.theory.FloatingPointTheory
//
//object smttest {
//  var myEnv = new Environment  
//
//  
//  def idToSort(id : Identifier) : uppsat.ast.Sort = {
//    id match {
//      case Identifier(SSymbol("Bool"), List()) => uppsat.theory.BooleanTheory.BooleanSort      
//      case Identifier(SSymbol("Int"), List()) => uppsat.theory.IntegerTheory.IntegerSort
//      case Identifier(SSymbol("FloatingPoint"), List(eBits, sBits)) => {
//        val (e, s) = 
//          (eBits, sBits) match {
//          case (SNumeral(i1), SNumeral(i2)) => (i1, i2)
//        }
//        uppsat.theory.FloatingPointTheory.FPSortFactory(List(e, s))
//      }
//      case unkSort => throw new Exception("Unknown sort: " + unkSort + "(" + unkSort.getClass +")")
//    }    
//  }
//  
//  
//  def qidToSymbol(qid : QualifiedIdentifier, sort : Option[List[uppsat.ast.ConcreteSort]] = None) : uppsat.ast.ConcreteFunctionSymbol = {
//    val name = qid.id.symbol.name.toString
//    if (myEnv.find(name).isDefined) {
//      myEnv.find(name).get
//    } else {
//      qid match { 
//        case QualifiedIdentifier(Identifier(SSymbol("="), List()), None) => {
//          sort.get.head match {
//            case IntegerSort => uppsat.theory.IntegerTheory.IntEquality
//            case BooleanSort => uppsat.theory.BooleanTheory.BoolEquality
//            case fp : FPSort => uppsat.theory.FloatingPointTheory.FPEqualityFactory(List(fp))            
//            case s => throw new Exception("Unsupported equality: " + s)
//          }
//        }
//        case QualifiedIdentifier(Identifier(SSymbol("+"), List()), None) => {
//          sort.get.head match {
//            case IntegerSort => uppsat.theory.IntegerTheory.IntAddition
//            case s => throw new Exception("Unsupported addition: " + s)
//          }
//        }
//        case QualifiedIdentifier(Identifier(SSymbol("RTP"), List()), None) => {
//          uppsat.theory.FloatingPointTheory.RoundToPositive
//        }
//        case QualifiedIdentifier(Identifier(SSymbol("fp.add"), List()), None) => {
//          uppsat.theory.FloatingPointTheory.FPAdditionFactory(List(sort.get(1)))
//        }
//        
//        case QualifiedIdentifier(Identifier(SSymbol("and"), List()), None) => {
//          uppsat.theory.BooleanTheory.BoolConjunction
//        }        
//        
//        case QualifiedIdentifier(id, list) => {
//          println("unhandled qi")
//          println("\t" + id)
//          println("\t" + list)
//          throw new Exception("...")
//          
//        }
//        
//      }
//    }
//  }
//  
//  def translateTerm(term : Term) : AST= {
//    term match {
//      case qi : QualifiedIdentifier => Leaf(qidToSymbol(qi))
//      case SNumeral(i) => uppsat.theory.IntegerTheory.IntLiteral(i)
//      case FunctionApplication(fun, terms) => {
//        // HACK for now ...
//        
//        if (fun.toString == "fp") {
//          uppsat.theory.FloatingPointTheory.parseLiteral(term.toString)
//        } else {
//          val transTerms = terms.map(translateTerm)
//          val transFun = qidToSymbol(fun, Some(transTerms.map(_.symbol.sort).toList))
//          AST(transFun, transTerms.toList)
//        }
//      }
//    }
//  }
//  
//  def test(filename : String) = {
//    myEnv = new Environment
//
//    val is = new java.io.FileReader(filename)
//    val lexer = new smtlib.lexer.Lexer(is)
//    val parser = new smtlib.parser.Parser(lexer)
//    
//    import smtlib.parser.Commands._
//    import scala.collection.mutable.ListBuffer
//    
//    val script: List[Command] = {
//      var cmds = new ListBuffer[Command]
//      var cmd = parser.parseCommand
//      while(cmd != null) {
//        cmds.append(cmd)
//        cmd = parser.parseCommand
//      }
//      cmds.toList
//    }    
//    
//    for (cmd <- script) {       
//      cmd match {
//        case Assert(term) => {
//          myEnv.addAssumption(translateTerm(term))
//        }
//        case CheckSat() => {
//          myEnv.print
//          val formula = myEnv.assumptions.head
//          val translator = new uppsat.solver.SMTTranslator(uppsat.theory.FloatingPointTheory)
//          val approximation = uppsat.approximation.SmallFloatsApproximation
//          println("CHECK SAT")
//          uppsat.ApproximationSolver.solve(formula, translator, approximation)          
//        }
//        case SetLogic(logic) => println("Setting logic: " + logic)
//        case DeclareFun(name, paramSorts, returnSort) => {
//          val transName = name.name
//          val transReturnSort = idToSort(returnSort.id)
//          if (paramSorts.isEmpty) { 
//            // Variable?
//            val symbol = 
//              transReturnSort match {
//                case uppsat.theory.BooleanTheory.BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(transName)
//                case uppsat.theory.IntegerTheory.IntegerSort => new uppsat.theory.IntegerTheory.IntVar(transName)
//                case fp : uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort => new uppsat.theory.FloatingPointTheory.FPVar(transName, fp)
//              }
//            myEnv.addSymbol(transName, symbol)
//          }
//        }
//        case GetModel() => {
//          //throw new Exception("get-model unsupported...")
//        }
//        case unknown => throw new Exception("Unknown command: " + unknown.getClass)        
//      }    
//    }
//  }
//}