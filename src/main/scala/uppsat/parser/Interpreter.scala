package uppsat.parser

import uppsat.theory.IntegerTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.BooleanTheory._

import smtlib._
import smtlib.Absyn._
import java.io._
import scala.collection.JavaConversions._
import uppsat.theory.FloatingPointTheory.RoundingModeSort
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory.RoundingMode
import uppsat.theory.FloatingPointTheory.FPConstantFactory
import uppsat.theory.FloatingPointTheory.FPSortFactory
import uppsat.solver.SMTSolver

case class SMTParserException(msg : String) extends Exception(msg)

object Interpreter {
  class SMTParser extends smtlib.Absyn.ScriptC.Visitor[Int, Object] {
    def visit(t : smtlib.Absyn.Script, o : Object) : Int = {
      for (i <- 0 until t.listcommand_.iterator.length) { 
        val c = t.listcommand_(i)        
        parse(c)
      }
      0
    }
  }

  def interpret(script : smtlib.Absyn.ScriptC) : Int = {
    interpretExp(script, null)
  }

  def interpretExp(script : smtlib.Absyn.ScriptC, o : Object) = {
    script.accept(new SMTParser(), o)
  }

  def interpretCommand(command : smtlib.Absyn.Command, o : Object) = {
    println("Command: " + command)
  }
  
  private def parse(script : Script) : Unit =
    for (cmd <- script.listcommand_) parse(cmd)

     
  protected def checkArgs(op : String, expected : Int, args : Seq[Term]) : Unit =
    if (expected != args.size)
      throw new SMTParserException(
        "Function \"" + op +
        "\" is applied to a wrong number of arguments: " +
        args.map(translateTerm).mkString("\n"))    
    
  var myEnv = new Environment

  def warn(msg : String) : Unit = {
    println("Warning: " + msg)
  }

  def asString(s : SymbolRef) : String = s match {
    case s : IdentifierRef     => asString(s.identifier_)
    case s : CastIdentifierRef => asString(s.identifier_)
  }
  
  def asString(id : Identifier) : String = id match {
    case id : SymbolIdent =>
      asString(id.symbol_)
    case id : IndexIdent =>
      asString(id.symbol_) + "_" +
      ((id.listindexc_ map (_.asInstanceOf[Index].numeral_)) mkString "_")
  }
  
  def asString(s : Symbol) : String = s match {
    case s : NormalSymbol =>
      s.normalsymbolt_
    case s : QuotedSymbol =>
      s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1)
  }

  object PlainSymbol {
    def unapply(s : SymbolRef) : scala.Option[String] = s match {
      case s : IdentifierRef => s.identifier_ match {
        case id : SymbolIdent => id.symbol_ match {
          case s : NormalSymbol => Some(s.normalsymbolt_)
          case _ => None
        }
        case _ => None
      }
      case _ => None
    }
  }
  protected def translateTerm(t : Term) : uppsat.ast.AST = {
      t match {
      case t : smtlib.Absyn.ConstantTerm =>
        translateSpecConstant(t.specconstant_)
      case t : FunctionTerm =>    
        symApp(t.symbolref_, t.listterm_)
      case t : NullaryTerm =>
        symApp(t.symbolref_, List())     
      case _ => throw new SMTParserException("Unknown term: " + t.toString())
    }
  }

  protected def translateSpecConstant(c : SpecConstant) : uppsat.ast.AST = {
    c match {
      case c : NumConstant => {
        uppsat.ast.Leaf(uppsat.theory.IntegerTheory.IntLiteral(c.numeral_.toInt))
      }
      case c : RatConstant => {
        val bits = java.lang.Long.toBinaryString(java.lang.Double.doubleToRawLongBits(c.rational_.toDouble))
        // TODO: We always store rationals as floats, good? bad? probably we should use reals.
        // TODO: Is the leading bits dropped
        val allBits = (("0" * (64 - bits.length)) ++ bits).map(_.toString.toInt)
        val sign = allBits.head
        val eBits = allBits.tail.take(11).map(_.toInt).toList
        val sBits = allBits.tail.drop(11).map(_.toInt).toList
        
        // TODO: Should this be 53,11 or 52,11?
        val fpsort = FPSortFactory(List(11, 53))
        uppsat.ast.Leaf(FloatingPointTheory.FPLiteral(sign.toInt, eBits, sBits, fpsort))
      }
  //    case c : HexConstant =>
  //      (MyIntLit(c.hexadecimal_ substring (2, 16)), SMTInteger)
  //    case c : BinConstant =>
  //      val binPattern = "\\#b(\\d+)".r
  //      val binPattern(bits) = c.binary_
  //      val bitList = bits.map(_.toString.toInt).toList
  //      throw new Exception(bitList + " (" + bitList.getClass + ")")
        //(MyIntLit(c.binary_ substring (2, 2)), SMTInteger)
      case  c => {
        throw new Exception("Unknown SpecConstant: " + c + " (" + c.getClass +")")
      }
    }
  }

 

  private def parse(cmd : Command) : Unit = cmd match {

    case cmd : SetLogicCommand => {
      println("Ignoring set-logic command")
    }

      //////////////////////////////////////////////////////////////////////////

    case cmd : SetOptionCommand => {
      println("Ignoring set-option command")
    }

  //     //////////////////////////////////////////////////////////////////////////
      
     case cmd : SetInfoCommand =>
       println("Ignoring set-info command")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : SortDeclCommand =>
       throw new SMTParserException("Sort Declaration Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : SortDefCommand =>
       throw new SMTParserException("Sort Definition Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////
      
    case cmd : FunctionDeclCommand => {
      val fullname = asString(cmd.symbol_)
      val name = if (fullname contains ':') "|" + fullname + "|" else fullname
      cmd.mesorts_ match {
        case _ : NoSorts => {
          val res = translateSort(cmd.sort_) 
          val symbol = res match {
            case IntegerSort => new uppsat.theory.IntegerTheory.IntVar(name)
            case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
            case fp : FPSort => new uppsat.theory.FloatingPointTheory.FPVar(name, fp)
          }

          myEnv.addSymbol(fullname, symbol)
        }
        case _ => throw new SMTParserException("Function Declaration with arguments unsupported")
      }
    }

  //     //////////////////////////////////////////////////////////////////////////

    case cmd : ConstDeclCommand => {
      val name = asString(cmd.symbol_)
      val res = translateSort(cmd.sort_)

      val symbol = 
        res match {
          case IntegerSort => new uppsat.theory.IntegerTheory.IntVar(name)
          case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
          case sort => throw new SMTParserException("Unsupported sort: " + sort)
        }

      myEnv.addSymbol(name, symbol)
    }

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : FunctionDefCommand => {
       val fullname = asString(cmd.symbol_)
       val name = if (fullname contains ':') "|" + fullname + "|" else fullname
       if (!cmd.listesortedvarc_.isEmpty) {
         throw new SMTParserException("Function Definitions with arguments unsupported")
       } else {
         val resType = translateSort(cmd.sort_)
         val body = translateTerm(cmd.term_)
         val symbol =
           resType match {
             case IntegerSort => new uppsat.theory.IntegerTheory.IntVar(name)
             case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
             case fp : FPSort => new uppsat.theory.FloatingPointTheory.FPVar(name, fp)
             case RoundingModeSort => new uppsat.theory.FloatingPointTheory.RMVar(name)
           }         
         myEnv.addDefinition(name, symbol, body)
       }
     }

  //     //////////////////////////////////////////////////////////////////////////
      
     case cmd : PushCommand =>
       throw new SMTParserException("Push Command unsupported")

     case cmd : PopCommand =>
       throw new SMTParserException("Pop Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////
      
    case cmd : AssertCommand => {
      val t = translateTerm(cmd.term_)
      myEnv.addAssumption(t)
    }

  //     //////////////////////////////////////////////////////////////////////////
    case cmd : CheckSatCommand => {
      val formula = myEnv.getFormula
      val translator = new uppsat.solver.SMTTranslator(uppsat.theory.FloatingPointTheory)
      val approximation = uppsat.approximation.SmallFloatsApproximation
      
      println("-----------------------------------------------")
      println("Starting Approximation Framework")
      println("-----------------------------------------------")        
      
      uppsat.ApproximationSolver.solve(formula, translator, approximation)
    }
  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetAssertionsCommand =>
       throw new SMTParserException("Get Assertions Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetValueCommand => 
       throw new SMTParserException("Get-Value Command unsupported")
       
  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetProofCommand =>
       throw new SMTParserException("Get-Proof Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetUnsatCoreCommand =>
       throw new SMTParserException("Get-Unsat-Core Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetAssignmentCommand =>
       throw new SMTParserException("Get-Assignment Command unsupported")

//     //////////////////////////////////////////////////////////////////////////

     case cmd : GetModelCommand =>
       throw new SMTParserException("Get-Model Command unsupported")
//     //////////////////////////////////////////////////////////////////////////
      
     case cmd : GetInfoCommand =>
       cmd.annotattribute_ match {
         case ":authors" =>
           throw new SMTParserException("Get-Info Authors Command unsupported")
         case ":name" =>
           println("(:name \"uppsat\")")
         case ":version" =>
           println("(:version 0.01)")
         case ":error-behavior" =>
           println("(:error-behavior \"immediate-exit\")")
         case ":interpolation-method" =>
           throw new SMTParserException("Get-Info Interpolation-Method Command unsupported")
         case ":reason-unknown" =>
           throw new SMTParserException("Get-Info Reason-Uknown Command unsupported")           
         case other => throw new SMTParserException("Get-Info " + other + " unsupported")
       }
      
  //     //////////////////////////////////////////////////////////////////////////
      
     case cmd : GetOptionCommand =>
       throw new SMTParserException("Get-Option Command unsupported")
      
  //     //////////////////////////////////////////////////////////////////////////
      
     case cmd : EchoCommand => 
       throw new SMTParserException("Get-Echo Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : ResetCommand =>
       throw new SMTParserException("Reset Command unsupported")

  //     //////////////////////////////////////////////////////////////////////////

    case cmd : ExitCommand =>
      println("Ignoring exit-command")

  //     //////////////////////////////////////////////////////////////////////////

     case _ : EmptyCommand => ()

  //     //////////////////////////////////////////////////////////////////////////

     case other =>
       throw new SMTParserException("Unsupported command: " + other)  
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def translateSort(s : Sort) : uppsat.ast.Sort = {
    val fpPattern = "FloatingPoint\\_(\\d+)\\_(\\d+)".r
    s match {
      case s : IdentSort => asString(s.identifier_) match {
        case "Int" => IntegerSort
        case "Bool" => BooleanSort
        case "RoundingMode" => RoundingModeSort
        case fpPattern(eBits, sBits) => uppsat.theory.FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
        case id => {
          throw new Exception("Unknown sort...:" + asString(s.identifier_))
        }
      }
    }
  }
  
  // //////////////////////////////////////////////////////////////////////////////
  
  def symApp(sym : SymbolRef, args : Seq[Term]) : uppsat.ast.AST = {
    sym match {
           

    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded connectives of formulae
      
    case PlainSymbol("true") => {
      uppsat.ast.Leaf(BoolTrue)
    }
    case PlainSymbol("false") => {
      uppsat.ast.Leaf(BoolFalse)
    }

    case PlainSymbol("not") => {
       uppsat.ast.AST(BoolNegation, List(translateTerm(args.head)))
    }
    
    // TODO: This could be more than 2 arguments!
    case PlainSymbol("and") => {
       uppsat.ast.AST(BoolConjunction, List(translateTerm(args(0)), translateTerm(args(1))))
    }    
            
    // case PlainSymbol("or") =>
    //   (connect(for (s <- flatten("or", args))
    //   yield asFormula(translateTerm(s, polarity)),
    //     IBinJunctor.Or),
    //     SMTBool)
      
    // case PlainSymbol("=>") => {
    //   if (args.size == 0)
    //     throw new Parser2InputAbsy.TranslationException(
    //       "Operator \"=>\" has to be applied to at least one argument")

    //   (connect((for (a <- args.init) yield
    //     !asFormula(translateTerm(a, -polarity))) ++
    //     List(asFormula(translateTerm(args.last, polarity))),
    //     IBinJunctor.Or),
    //     SMTBool)
    // }
      
    // case PlainSymbol("xor") => {
    //   if (args.size == 0)
    //     throw new Parser2InputAbsy.TranslationException(
    //       "Operator \"xor\" has to be applied to at least one argument")

    //   (connect(List(asFormula(translateTerm(args.head, polarity))) ++
    //     (for (a <- args.tail) yield
    //       !asFormula(translateTerm(a, -polarity))),
    //     IBinJunctor.Eqv),
    //     SMTBool)
    // }
      
    // case PlainSymbol("ite") => {
    //   checkArgNum("ite", 3, args)
    //   val transArgs = for (a <- args) yield translateTerm(a, 0)
    //     (transArgs map (_._2)) match {
    //     case Seq(SMTBool, SMTBool, SMTBool) =>
    //       (IFormulaITE(asFormula(transArgs(0)),
    //         asFormula(transArgs(1)), asFormula(transArgs(2))),
    //         SMTBool)
    //     case Seq(SMTBool, t1, t2) =>
    //       (ITermITE(asFormula(transArgs(0)),
    //         asTerm(transArgs(1)), asTerm(transArgs(2))),
    //         t1)
    //   }
    // }

    
    case PlainSymbol("+") => {
      checkArgs("+", 2, args)
      translateTerm(args(0)) + translateTerm(args(1))
    }
    
    case PlainSymbol("-") => {
      if (args.length == 1) {
        - translateTerm(args(0))
      } else {
        throw new Exception("Only unary minus supported...")
      }
    }      
    
    
    //   ////////////////////////////////////////////////////////////////////////////
    //   // Hardcoded predicates (which might also operate on booleans)
      
    case PlainSymbol("=") => {
      if (args.length != 2) {
        throw new Exception("Not two arguments for = ...")
      } else {
        val lhs = translateTerm(args(0))
        val rhs = translateTerm(args(1))
        translateTerm(args(0)) === translateTerm(args(1))
      }
    }
    
    // 
    //  FLOATING POINT SYMBOLS
    //

    case PlainSymbol("fp.neg") => {
      if (args.length != 1) {
        throw new Exception("Not one argument for fp.neg...")
      } else {
        - translateTerm(args(0))
      }
    }      
    
    case PlainSymbol("fp.lt") => {
      if (args.length != 2) {
        throw new Exception("Not two arguments for fp.leq ...")
      } else {
        translateTerm(args(0)) < translateTerm(args(1))
      }
    }    
    
    case PlainSymbol("fp.leq") => {
      if (args.length != 2) {
        throw new Exception("Not two arguments for fp.leq ...")
      } else {
        translateTerm(args(0)) <= translateTerm(args(1))
      }
    }

    case PlainSymbol("fp.add") => {
      checkArgs("fp.add", 3, args)
      translateTerm(args(0)).symbol.sort match {
        case RoundingModeSort => {
          implicit val roundingMode = args(0)
          translateTerm(args(1)) + translateTerm(args(2))
        }
        case _ => throw new SMTParserException("First argument of fp.add not roundingmode") 
      }      
    }

    case PlainSymbol("fp.div") => {
      if (args.length != 3) {
        throw new Exception("Not two arguments for fp.mul ...")
      } else {
        if (!(translateTerm(args(0)).symbol.sort == RoundingModeSort))
          throw new Exception("First argument not roundingmode...")
        implicit val roundingMode = args(0)
        translateTerm(args(1)) / translateTerm(args(2))
      }
    }      
    
    case PlainSymbol("fp.mul") => {
      if (args.length != 3) {
        throw new Exception("Not two arguments for fp.mul ...")
      } else {
        if (!(translateTerm(args(0)).symbol.sort == RoundingModeSort))
          throw new Exception("First argument not roundingmode...")
        implicit val roundingMode = args(0)
        translateTerm(args(1)) * translateTerm(args(2))
      }
    }  
    
    case PlainSymbol("RTP") => {
      FloatingPointTheory.RoundToPositive
    }
    case PlainSymbol("roundTowardZero") => {
      FloatingPointTheory.RoundToZero
    }

    case PlainSymbol("roundNearestTiesToEven") => {
      FloatingPointTheory.RoundToNearestTiesToEven
    }    
     
    // case PlainSymbol("<=") =>
    //   (translateChainablePred(args, _ <= _), SMTBool)
    // case PlainSymbol("<") =>
    //   (translateChainablePred(args, _ < _), SMTBool)
    // case PlainSymbol(">=") =>
    //   (translateChainablePred(args, _ >= _), SMTBool)
    // case PlainSymbol(">") =>
    //   (translateChainablePred(args, _ > _), SMTBool)
      
    // case IndexedSymbol("divisible", denomStr) => {
    //   checkArgNum("divisible", 1, args)
    //   val denom = i(IdealInt(denomStr))
    //   val num = VariableShiftVisitor(asTerm(translateTerm(args.head, 0)), 0, 1)
    //   (ex(num === v(0) * denom), SMTBool)
    // }
      
    //   ////////////////////////////////////////////////////////////////////////////
    //   // Hardcoded integer operations


    // case PlainSymbol("-") if (args.length == 1) =>
    //   (-asTerm(translateTerm(args.head, 0), SMTInteger), SMTInteger)

    // case PlainSymbol("~") if (args.length == 1) => {
    //   if (!tildeWarning) {
    //     warn("interpreting \"~\" as unary minus, like in SMT-LIB 1")
    //     tildeWarning = true
    //   }unintFunApp
    //   (-asTerm(translateTerm(args.head, 0), SMTInteger), SMTInteger)
    // }

    // case PlainSymbol("-") => {
    //   (asTerm(translateTerm(args.head, 0), SMTInteger) -
    //     sum(for (a <- args.tail)
    //     yield asTerm(translateTerm(a, 0), SMTInteger)),
    //     SMTInteger)
    // }

    // case PlainSymbol("*") =>
    //   ((for (s <- flatten("*", args))
    //   yield asTerm(translateTerm(s, 0), SMTInteger))
    //     reduceLeft (mult _),
    //     SMTInteger)

    // case PlainSymbol("div") => {
    //   checkArgNum("div", 2, args)
    //   val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
    //   (mulTheory.eDiv(num, denom), SMTInteger)
    // }
      
    // case PlainSymbol("mod") => {
    //   checkArgNum("mod", 2, args)
    //   val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
    //   (mulTheory.eMod(num, denom), SMTInteger)
    // }

    // case PlainSymbol("abs") => {
    //   checkArgNum("abs", 1, args)
    //   (abs(asTerm(translateTerm(args.head, 0))), SMTInteger)
    // }
      
      ////////////////////////////////////////////////////////////////////////////
      // Array operations
      
    // case PlainSymbol("select") => {
    //   val transArgs = for (a <- args) yield translateTerm(a, 0)
    //   transArgs.head._2 match {
    //     case SMTArray(_, resultType) =>
    //       (MyFunApp(SimpleArray(args.size - 1).select,
    //         for (a <- transArgs) yield asTerm(a)),
    //         resultType)
    //     case s =>
    //       throw new Exception(
    //         "select has to be applied to an array expression, not " + s)
    //   }
    // }

    // case PlainSymbol("store") => {
    //   val transArgs = for (a <- args) yield translateTerm(a, 0)
    //   transArgs.head._2 match {
    //     case s : SMTArray =>
    //       (IFunApp(SimpleArray(args.size - 2).store,
    //         for (a <- transArgs) yield asTerm(a)),
    //         s)
    //     case s =>
    //       throw new Exception(
    //         "store has to be applied to an array expression, not " + s)
    //   }
    // }
    
    case PlainSymbol("fp") => {
      def bitTermToBitList(term : Term) : List[Int] = {
        term match {
          case t : smtlib.Absyn.ConstantTerm =>
            t.specconstant_ match {
              case c : BinConstant => { 
                val binPattern = "\\#b(\\d+)".r
                val binPattern(bits) = c.binary_
                bits.map(_.toString.toInt).toList
              }
            }
        }
      }      
      val transArgs = args.map(bitTermToBitList)
      val signBit = transArgs(0)(0)
      val eBits = transArgs(1)
      val sBits = transArgs(2)
      val fpsort = uppsat.theory.FloatingPointTheory.FPSortFactory(List(eBits.length, sBits.length+1))
      uppsat.ast.Leaf(uppsat.theory.FloatingPointTheory.FPLiteral(signBit, eBits, sBits, fpsort))
    }
    
//    case PlainSymbol(ps) if ("to\\_\\fp\\_(\\d+)\\_(\\d+)".r.findFirstIn(asString(sym)).isDefined) => {
    case _ if ("to".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "to_fp_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val targetSort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val s = FloatingPointTheory.FPToFPFactory(List(targetSort))
          uppsat.ast.AST(s, List(translateTerm(args(0)), translateTerm(args(1))))
        }
      }
    }
    
    case _ if ("\\+oo".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "\\+oo_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPPlusInfinity(List(sort))
          uppsat.ast.AST(value, List())
        }
      }
    }
    
    case _ if ("-oo".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "-oo_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPMinusInfinity(List(sort))
          uppsat.ast.AST(value, List())
        }
      }
    }    
    
   
    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => {
      // TODO: We should maybe not use strings as IDs?
      (myEnv.findSymbol(asString(id)), myEnv.findDefinition(asString(id))) match {
        case (Some(symbol), _) =>
          uppsat.ast.Leaf(symbol)
        case (_, Some(ast)) => ast
        case (None, None) => {
          myEnv.print
          id match {
            case PlainSymbol(smth) => println("\t" + smth)
            case _ => println(id.getClass)
          }
          throw new Exception("Undefined symbol: " + asString(id))
        }
      }
//      println("Bailing out on uniterpreted formula: " + asString(id))
//      unintFunApp(asString(id), sym, args, polarity)
    }
  }
  }

  // TODO: What does this do?
  private def unintFunApp(id : String,
    sym : SymbolRef, args : Seq[Term], polarity : Int)
      : uppsat.ast.AST = {
    val funSort = myEnv.lookup(id)
    throw new Exception("Cannot handle uninterpreted function applications")    
  }

    // (env lookupSym id) match {
    //   case Environment.Predicate(pred, _, _) => {
    //     checkArgNumLazy(printer print sym, pred.arity, args)
    //     (IAtom(pred, for (a <- args) yield asTerm(translateTerm(a, 0))),
    //       SMTBool)
    //   }
        
    //   case Environment.Function(fun, SMTFunctionType(_, resultType)) => {
    //     checkArgNumLazy(printer print sym, fun.arity, args)
    //       (functionDefs get fun) match {
    //       case Some((body, t)) => {
    //         var translatedArgs = List[ITerm]()
    //         for (a <- args)
    //           translatedArgs = asTerm(translateTerm(a, 0)) :: translatedArgs
    //         (VariableSubstVisitor(body, (translatedArgs, 0)), t)
    //       }
    //       case None =>
    //         (IFunApp(fun, for (a <- args) yield asTerm(translateTerm(a, 0))),
    //           resultType)
    //     }
    //   }

    //   case Environment.Constant(c, _, t) =>
    //     (c, t)
        
    //   case Environment.Variable(i, BoundVariable(t)) =>
    //     (v(i), t)
        
    //   case Environment.Variable(i, SubstExpression(e, t)) =>
    //     (e, t)
    // }
}