package uppsat.parser

import uppsat.theory.IntegerTheory._
import uppsat.globalOptions.verbose

import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.BooleanTheory._
import uppsat.theory.RealTheory._

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
import uppsat.approximation.PostOrderNodeBasedApproximation
import uppsat.approximation.IJCARSmallFloatsApp
import uppsat.ApproximationSolver

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
  
  def reset() = {
      myEnv = new Environment
  }
  
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
//      case c : NumConstant => {
//        //uppsat.ast.Leaf(uppsat.theory.RealTheory.RealNumeral(BigInt(c.numeral_.toString)))
//      }
      case c : RatConstant => 
        //uppsat.ast.Leaf(uppsat.theory.RealTheory.RealDecimal(BigDecimal(c.rational_.toString())))
        
      {
        val bits = java.lang.Long.toBinaryString(java.lang.Double.doubleToRawLongBits(c.rational_.toDouble))
        // TODO: We always store rationals as floats, good? bad? probably we should use reals.
        // TODO: Is the leading bits dropped
        val allBits = (("0" * (64 - bits.length)) ++ bits).map(_.toString.toInt)
        val sign = allBits.head
        val eBits = allBits.tail.take(11).map(_.toInt).toList
        val sBits = allBits.tail.drop(11).map(_.toInt).toList
        
        // TODO: Should this be 53,11 or 52,11?
        val fpsort = FPSortFactory(List(11, 53))
        uppsat.ast.Leaf(FloatingPointTheory.FloatingPointLiteral(sign.toInt, eBits, sBits, fpsort))
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
      verbose("Ignoring set-logic command")
    }

      //////////////////////////////////////////////////////////////////////////

    case cmd : SetOptionCommand => {
      verbose("Ignoring set-option command")
    }

  //     //////////////////////////////////////////////////////////////////////////
      
     case cmd : SetInfoCommand =>
       verbose("Ignoring set-info command")

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
            case RealSort => new uppsat.theory.RealTheory.RealVar(name)
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
          case RealSort => new uppsat.theory.RealTheory.RealVar(name)
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
      val formula = myEnv.getFormula.labelAST     
      val translator = new uppsat.solver.SMTTranslator(uppsat.theory.FloatingPointTheory)
      val approximation = uppsat.globalOptions.getApproximation//uppsat.approximation.SmallFloatsApproximation
      // TODO:  Hooks to user defined approximation
      myEnv.result = ApproximationSolver.Unknown
      myEnv.result = uppsat.ApproximationSolver.solve(formula, translator, approximation)
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
        case "Real" => RealSort
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
   
 
  def symApp(sym : SymbolRef, args : Seq[Term]) : uppsat.ast.AST =
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
      if (args.length > 2)
        throw new SMTParserException("and with more than 2 arguments...")
      uppsat.ast.AST(BoolConjunction, List(translateTerm(args(0)), translateTerm(args(1))))
    }    
    
    case PlainSymbol("+") => {
      checkArgs("+", 2, args)
      translateTerm(args(0)) + translateTerm(args(1))
    }
    
    case PlainSymbol("-") => {
      checkArgs("-", 1, args)
      -translateTerm(args(0))
    }      
    
    case PlainSymbol("*") => {
      checkArgs("*", 2, args)
      translateTerm(args(0)) * translateTerm(args(1))
    }
    
    case PlainSymbol("/") => {
      checkArgs("/", 2, args)
      translateTerm(args(0)) / translateTerm(args(1))
    }
    
    
    //   ////////////////////////////////////////////////////////////////////////////
    //   // Hardcoded predicates (which might also operate on booleans)
      
    case PlainSymbol("=") => {
      checkArgs("=", 2, args)
      translateTerm(args(0)) === translateTerm(args(1))
    }
    
    case PlainSymbol("<") => {
      checkArgs("<", 2, args)
      translateTerm(args(0)) < translateTerm(args(1))
    }
    
    case PlainSymbol("<=") => {
      checkArgs("<=", 2, args)
      translateTerm(args(0)) <= translateTerm(args(1))
    }
    
    case PlainSymbol(">") => {
      checkArgs(">", 2, args)
      translateTerm(args(0)) > translateTerm(args(1))
    }
    
    case PlainSymbol(">=") => {
      checkArgs(">=", 2, args)
      translateTerm(args(0)) >= translateTerm(args(1))
    }
    
    
    // 
    //  FLOATING POINT SYMBOLS
    //

    
    case PlainSymbol("fp.neg") => {
      checkArgs("fp.neg", 1, args)
      -translateTerm(args(0))
    }      
    
    case PlainSymbol("fp.lt") => {
      checkArgs("fp.lt", 2, args)
      translateTerm(args(0)) < translateTerm(args(1))
    }    
    
    case PlainSymbol("fp.leq") => {
      checkArgs("fp.leq", 2, args)
      translateTerm(args(0)) <= translateTerm(args(1))
    }
    
    case PlainSymbol("fp.gt") => {
      checkArgs("fp.gt", 2, args)
      translateTerm(args(0)) > translateTerm(args(1))
    }    
    
    case PlainSymbol("fp.geq") => {
      checkArgs("fp.geq", 2, args)
      translateTerm(args(0)) >= translateTerm(args(1))
    }
    
    case PlainSymbol("fp.eq") => {
      checkArgs("fp.eq", 2, args)
       translateTerm(args(0)) === translateTerm(args(1))
    }
    
    // We can't use syntactic sugar since first leaf might not be a rounding-mode but rather a defined function
    case PlainSymbol("fp.add") => {
      checkArgs("fp.add", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPAdditionFactory(List(fp1, fp1, fp1)), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.add: " + ((s1, s2, s3)))
      }    
    }
    
    case PlainSymbol("fp.mul") => {
      checkArgs("fp.mul", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPMultiplicationFactory(List(fp1, fp1, fp1)), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.mul: " + ((s1, s2, s3)))
      }    
    }    
    
    case PlainSymbol("fp.div") => {
      checkArgs("fp.div", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPDivisionFactory(List(fp1, fp1, fp1)), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.div: " + ((s1, s2, s3)))
      }    
    }    
            
    case PlainSymbol("RTP") => FloatingPointTheory.RoundToPositive
    case PlainSymbol("roundTowardZero") => FloatingPointTheory.RoundToZero
    case PlainSymbol("roundNearestTiesToEven") => FloatingPointTheory.RoundToNearestTiesToEven
    case PlainSymbol("RNE") => FloatingPointTheory.RoundToNearestTiesToEven
     
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
      uppsat.ast.Leaf(uppsat.theory.FloatingPointTheory.FloatingPointLiteral(signBit, eBits, sBits, fpsort))
    }
    

    // Floating point functions
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
    
    // Floating point special numbers
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
    }
  }
}