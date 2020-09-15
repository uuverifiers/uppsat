// Thank you Philipp and Princess!

package uppsat.parser

import uppsat.theory.IntegerTheory._

import uppsat.globalOptions.verbose
import uppsat.globalOptions.VERSION

import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.BitVectorTheory.BVSortFactory.BVSort
import uppsat.theory.BitVectorTheory._
import uppsat.theory.BooleanTheory._
import uppsat.theory.RealTheory._

import ap.parser.smtlib
import ap.parser.smtlib._
import ap.parser.smtlib.Absyn._
import java.io._
import scala.jdk.CollectionConverters._
// import scala.collection.JavaConverters._


import uppsat.theory.IntegerTheory

import uppsat.theory.FloatingPointTheory.RoundingModeSort
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory.RoundingMode
import uppsat.theory.FloatingPointTheory.FPConstantFactory
import uppsat.theory.FloatingPointTheory.FPSortFactory
import uppsat.solver.SMTSolver
import uppsat.approximation.fpa.smallfloats.IJCARSmallFloatsApp
import uppsat.ApproximationSolver
import uppsat.theory.RealTheory
import uppsat.theory.BitVectorTheory

case class SMTParserException(msg : String) extends Exception(msg)

object Interpreter {

def hexToBitList(hex : String) = {
        val list = hex.map { x =>
          x match {
            case '0' => List(0,0,0,0)
            case '1' => List(0,0,0,1)
            case '2' => List(0,0,1,0)
            case '3' => List(0,0,1,1)
            
            case '4' => List(0,1,0,0)
            case '5' => List(0,1,0,1)
            case '6' => List(0,1,1,0)
            case '7' => List(0,1,1,1)        
    
            case '8' => List(1,0,0,0)
            case '9' => List(1,0,0,1)
            case 'a' | 'A' => List(1,0,1,0)
            case 'b' | 'B' => List(1,0,1,1)

            case 'c' | 'C' => List(1,1,0,0)
            case 'd' | 'D' => List(1,1,0,1)
            case 'e' | 'E' => List(1,1,1,0)
            case 'f' | 'F' => List(1,1,1,1)
          }
        }
        list.flatten.toList
}



  class SMTParser extends smtlib.Absyn.ScriptC.Visitor[Int, Object] {
    def visit(t : smtlib.Absyn.Script, o : Object) : Int = {
      // for (i <- 0 until t.listcommand_.iterator.length) { 
      //   val c = t.listcommand_(i)        
      //   parse(c)
      // }

      //
      for (c <- t.listcommand_.iterator().asScala) {
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
    for (cmd <- script.listcommand_.iterator().asScala) parse(cmd)

     
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
      ((id.listindexc_.iterator().asScala.map(_.asInstanceOf[Index].numeral_)).mkString("_"))
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
          symApp(t.symbolref_, t.listterm_.iterator().asScala.toList)
      case t : NullaryTerm =>
        symApp(t.symbolref_, List())
      case t : LetTerm =>
        val bindings = (for (b <- t.listbindingc_.iterator().asScala) yield {
          val binding = b.asInstanceOf[Binding]
          val boundTerm = translateTerm(binding.term_)
          val fullname = asString(binding.symbol_)
          val name = fixName(fullname)
          (name, boundTerm)
        }).toList
        myEnv.pushLet(bindings)
        val ast = translateTerm(t.term_)
        myEnv.popLet()
        ast
      case _ => throw new SMTParserException("Unknown term: " + t.toString())
    }
  }

  protected def translateSpecConstant(c : SpecConstant) : uppsat.ast.AST = {
    c match {
      case c : NumConstant => {
        myEnv.theory match {
          case Some(uppsat.theory.FloatingPointTheory) => uppsat.ast.Leaf(uppsat.theory.RealTheory.RealNumeral(BigInt(c.numeral_.toString))) 
          case Some(uppsat.theory.IntegerTheory) => uppsat.ast.Leaf(uppsat.theory.IntegerTheory.IntLiteral(BigInt(c.numeral_.toString)))
          case _ => throw new Exception(s"NumConstant which is not of FloatingPoint or Integer theory: ${myEnv.theory}")
        }
      }
      case c : RatConstant if myEnv.theory ==  Some(FloatingPointTheory) => 
      {
        val bits = java.lang.Long.toBinaryString(java.lang.Double.doubleToRawLongBits(c.rational_.toDouble))
        // TODO: We always store rationals as floats, good? bad? probably we should use reals.
        // TODO: Is the leading bits dropped
        val allBits = (("0" * (64 - bits.length)) ++ bits).map(_.toString.toInt)
        val sign = allBits.head
        val eBits = allBits.tail.take(11).map(_.toInt).toList
        val sBits = allBits.tail.drop(11).map(_.toInt).toList
        
        val fpsort = FPSortFactory(List(11, 53))
        
        if (!eBits.contains(0))
          throw new Exception("Special number!")
        
        
        // MAJORTODO
        if (!eBits.contains(1) && !sBits.contains(1)) {
          val value = 
            if (sign == 0)
              FloatingPointTheory.FPPositiveZero(fpsort)
            else
              FloatingPointTheory.FPNegativeZero(fpsort)
          uppsat.ast.AST(value, List())
        } else {
          uppsat.ast.Leaf(uppsat.theory.FloatingPointTheory.FloatingPointLiteral(sign.toInt, eBits, sBits, fpsort))
        }
      }
        
      case c : RatConstant => {
        // RatConstant given as decimal number, convert to num/denum representation.
        // TODO: This is probably slow
        val bd = BigDecimal(c.rational_.toString()).toString
        val parts = bd.split("\\.")
        var num = BigInt(parts(0))
        var den = BigInt(1)
        val frac = parts(1)
        for (i <- 0 until frac.length()) {
          num *= 10
          den *= 10
        }
        num += BigInt(frac)
        val gcd = num.gcd(den)
        num /= gcd
        den /= gcd        
        uppsat.ast.Leaf(uppsat.theory.RealTheory.RealDecimal(num, den))
      }
        
        
    case c : HexConstant =>
      val hexPattern = "\\#x([0-9a-f]+)".r
      c.hexadecimal_ match {
        case hexPattern(hex) => {
          val bitList = hexToBitList(hex)
          val sort = BitVectorTheory.BVSortFactory(List(bitList.length))
          val value = BitVectorTheory.BitVectorLiteral(bitList, sort)
          uppsat.ast.Leaf(value)
        }
        case other => throw new Exception("Strange hexadecimal literal: " + other)
      }
  //      (MyIntLit(c.hexadecimal_ substring (2, 16)), SMTInteger)
      // TODO: (Aleks) Are Binary Constants always Bit Vectors?
      case c : BinConstant =>
        val binPattern = "\\#b(\\d+)".r
        val binPattern(bits) = c.binary_
        val bitList = bits.map(_.toString.toInt).toList
        val sort = BitVectorTheory.BVSortFactory(List(bitList.length))
        val value = BitVectorTheory.BitVectorLiteral(bitList, sort)
        uppsat.ast.Leaf(value)
//        (MyIntLit(c.binary_ substring (2, 2)), SMTInteger)
      case  c => {
        throw new Exception("Unknown SpecConstant: " + c + " (" + c.getClass +")")
      }
    }
  }

  def fixName(name : String) = {
    val specialChars = "#:"
    if (name.exists(specialChars.contains(_))) 
      "|" + name + "|"
    else
      name
  }

  private def parse(cmd : Command) : Unit = cmd match {
    
    case cmd : SetLogicCommand => {
      verbose("Ignoring set-logic command")
      asString(cmd.symbol_) match {
        case "QF_FP" => myEnv.setTheory(FloatingPointTheory)
        case "QF_FPBV" => myEnv.setTheory(FloatingPointTheory)
        case "QF_BV" => myEnv.setTheory(BitVectorTheory)
        case "QF_BVFP" => myEnv.setTheory(FloatingPointTheory)
        case "QF_LIA" => myEnv.setTheory(IntegerTheory)
        case _ => throw new Exception("unknown set-logic command : \n"  + asString(cmd.symbol_))
      }
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
      val name = fixName(fullname)
      cmd.mesorts_ match {
        case _ : NoSorts => {
          val res = translateSort(cmd.sort_) 
          val symbol = res match {
            case IntegerSort => {
              myEnv.theoryGuess = Some(uppsat.theory.IntegerTheory)
              new uppsat.theory.IntegerTheory.IntVar(name)
            }
            case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
            case RealSort => {
              myEnv.theoryGuess = Some(uppsat.theory.RealTheory)
              new uppsat.theory.RealTheory.RealVar(name)
            }
            case fp : FPSort => {
              myEnv.theoryGuess = Some(uppsat.theory.FloatingPointTheory)
              new uppsat.theory.FloatingPointTheory.FPVar(name, fp)
            }
            case bv : BVSort => {
              myEnv.theoryGuess = Some(uppsat.theory.BitVectorTheory)
              new uppsat.theory.BitVectorTheory.BVVar(name, bv)
            }
          }


          myEnv.addDeclaration(name, symbol)
        }
        case _ => throw new SMTParserException("Function Declaration with arguments unsupported")
      }
    }

  //     //////////////////////////////////////////////////////////////////////////

    case cmd : ConstDeclCommand => {
      val fullname = asString(cmd.symbol_)
      val name = fixName(fullname)
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
       val name = fixName(fullname)
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

      val usingTheory = 
        if (myEnv.theory.isDefined)
          myEnv.theory.get
        else
          uppsat.theory.FloatingPointTheory // Defaulting to FP since our project is currently focused on this.
//        else if (myEnv.theoryGuess.isDefined)
//          myEnv.theoryGuess.get
//        else throw new SMTParserException("No theory defined") 
      val translator = new uppsat.solver.SMTTranslator(usingTheory) 
      
      val approximation = uppsat.globalOptions.getApproximation
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

     case cmd : GetModelCommand => {
       myEnv.result match {
         case ApproximationSolver.Sat(model) => println(model.mkString("\n"))
         case _ => throw new SMTParserException("Get-Model Command with no model")
       }
       
     }
//     //////////////////////////////////////////////////////////////////////////
      
     case cmd : GetInfoCommand =>
       cmd.annotattribute_ match {
         case ":authors" =>
           throw new SMTParserException("Get-Info Authors Command unsupported")
         case ":name" =>
           println("(:name \"uppsat\")")
         case ":version" =>
           println("(:version " + uppsat.globalOptions.VERSION + ")")
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
    val bvPattern = "BitVec\\_(\\d+)".r
    s match {
      case s : IdentSort => asString(s.identifier_) match {
        case "Int" => IntegerSort
        case "Real" => RealSort
        case "Bool" => BooleanSort
        case "RoundingMode" => RoundingModeSort
        case "Float32" => uppsat.theory.FloatingPointTheory.FPSortFactory(List(8, 24))
        case fpPattern(eBits, sBits) => uppsat.theory.FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
        case bvPattern(bits) => uppsat.theory.BitVectorTheory.BVSortFactory(List(bits.toInt))
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
      val argCount = args.length
      val transArgs = args.map(translateTerm)
      val symbol = naryConjunction(argCount)
      uppsat.ast.AST(symbol, transArgs.toList)  
    }
    
    // TODO: This could be more than 2 arguments!
    case PlainSymbol("or") => {
      val argCount = args.length
      val transArgs = args.map(translateTerm)
      val symbol = naryDisjunction(argCount)
      uppsat.ast.AST(symbol, transArgs.toList)
    }    
    
    case PlainSymbol("=>") => {
      if (args.length > 2)
        throw new SMTParserException("=> with more than 2 arguments...")
      uppsat.ast.AST(BoolImplication, List(translateTerm(args(0)), translateTerm(args(1))))
    }        

    // TODO: This could be more than 2 arguments!
    case PlainSymbol("xor") => {
      if (args.length > 2)
        throw new SMTParserException("xor with more than 2 arguments...")
      uppsat.ast.AST(BoolExclusiveDisjunction, List(translateTerm(args(0)), translateTerm(args(1))))
    }    
    
    
    case PlainSymbol("+") => {
      checkArgs("+", 2, args)
      translateTerm(args(0)) + translateTerm(args(1))
    }
    
    case PlainSymbol("-") => {
      args.length match {
        case 1 => -translateTerm(args(0))
        case 2 => translateTerm(args(0)) - translateTerm(args(1))
      }
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

    case PlainSymbol("fp.isZero") => {
      checkArgs("fp.isZero", 1, args)
      val ta = translateTerm(args(0))
      uppsat.ast.AST(FloatingPointTheory.FPIsZeroFactory(ta.symbol.sort), List(ta))      
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
      val ta1 = translateTerm(args(0))
      val ta2 = translateTerm(args(1)) 
      uppsat.ast.AST(FloatingPointTheory.FPFPEqualityFactory(ta1.symbol.sort, ta2.symbol.sort), List(ta1, ta2))
    }
    
    // We can't use syntactic sugar since first leaf might not be a rounding-mode but rather a defined function
    case PlainSymbol("fp.add") => {
      checkArgs("fp.add", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPAdditionFactory(fp1, fp1, fp1), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.add: " + ((s1, s2, s3)))
      }    
    }
    
    case PlainSymbol("fp.sub") => {
      checkArgs("fp.sub", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPSubstractionFactory(fp1, fp1, fp1), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.sub: " + ((s1, s2, s3)))
      }    
    }    
    
    case PlainSymbol("fp.mul") => {
      checkArgs("fp.mul", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPMultiplicationFactory(fp1, fp1, fp1), ta.toList)
        case (s1, s2, s3) => 
          throw new SMTParserException("Wrong sorts for fp.mul: " + ((s1, s2, s3)))
      }    
    }    
    
    case PlainSymbol("fp.div") => {
      checkArgs("fp.div", 3, args)
      val ta = args.map(translateTerm)
      (ta(0).symbol.sort, ta(1).symbol.sort, ta(2).symbol.sort) match {
        case (RoundingModeSort, fp1 : FPSort, fp2 : FPSort) if (fp1 == fp2) =>
          uppsat.ast.AST(FloatingPointTheory.FPDivisionFactory(fp1, fp1, fp1), ta.toList)
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
              case h : HexConstant => {
                val hexPattern = "\\#x([a-fA-F0-9]+)".r
                val hexPattern(hex) = h.hexadecimal_
                hexToBitList(hex).map(_.toString.toInt).toList
                
              }
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
      if (!eBits.contains(1) && !sBits.contains(1)) {
        val value = FloatingPointTheory.FPPositiveZero(fpsort)
        uppsat.ast.AST(value, List())
      } else {
        uppsat.ast.Leaf(uppsat.theory.FloatingPointTheory.FloatingPointLiteral(signBit, eBits, sBits, fpsort))
      }
    }
    

    // Floating point functions
    case _ if ("to_fp_\\d+_\\d+".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "to_fp_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val targetSort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val s = FloatingPointTheory.FPToFPFactory(targetSort)
          // TODO: Why do we have two arguments here?
          uppsat.ast.AST(s, List(translateTerm(args(0)), translateTerm(args(1))))
          //uppsat.ast.AST(s, List(translateTerm(args(0))))
        }
      }
    }
    
    // Floating point special numbers
    case _ if ("\\+oo".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "\\+oo_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPPlusInfinity(sort)
          uppsat.ast.AST(value, List())
        }
      }
    }
    
    case _ if ("-oo".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "-oo_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPMinusInfinity(sort)
          uppsat.ast.AST(value, List())
        }
      }
    }    
    

    case _ if ("\\+zero_\\d+_\\d+".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "\\+zero_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPPositiveZero(sort)
          uppsat.ast.AST(value, List())
        }
      }
    }        

    case _ if ("\\-zero_\\d+_\\d+".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "\\-zero_(\\d+)_(\\d+)".r
      asString(sym) match {
        case p(eBits, sBits) => {
          val sort = FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
          val value = FloatingPointTheory.FPNegativeZero(sort)
          uppsat.ast.AST(value, List())
        }
      }
    }        
    
    
    // 
    //  BITVECTOR SYMBOLS
    //


    case _ if ("bv(\\d+)_(\\d+)".r.findFirstIn(asString(sym)).isDefined) => {
      
      def toBinary(n:Int, bin: List[Int] = List.empty[Int]) : List[Int] = {
        if(n/2 == 1) (1:: (n % 2) :: bin)
        if(n == 0) List(0)
        else {
          val r = n % 2
          val q = n / 2
          toBinary(q, r::bin)
        }
      }

      val p = "bv(\\d+)_(\\d+)".r
      checkArgs("bv", 0, args)
      asString(sym) match {
        case p(constant, bits) => {
          val sort = BVSort(bits.toInt)
          val constantBitList = toBinary(constant.toInt)
          val padding = List.fill(bits.toInt - constantBitList.length)(0)

          uppsat.ast.Leaf(uppsat.theory.BitVectorTheory.BitVectorLiteral(padding ++ constantBitList, sort))
        }
      }
    }


    // TODO: (Peter) This should be done more properly, probably with a val-defined pattern.
    // TODO: (Aleks) Should it be "sign_extend_1" or "sign_extend 1" (notice the underscore)
    case _ if ("sign_extend".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "sign_extend_(\\d+)".r
      checkArgs("sign_extend", 1, args)
      val arg = translateTerm(args(0))
      (asString(sym), arg.symbol.sort) match {
        case (p(count), BVSort(bits)) => {
          val sort = BVSort(count.toInt+bits)
          val value = BitVectorTheory.BVSignExtendFactory(count.toInt)(sort)
          uppsat.ast.AST(value, List(arg))
        }
      }
    }

    // TODO: (Aleks) Should it be "sign_extend_1" or "sign_extend 1" (notice the underscore)
    case _ if ("zero_extend".r.findFirstIn(asString(sym)).isDefined) => {
      val p = "zero_extend_(\\d+)".r
      checkArgs("zero_extend", 1, args)
      val arg = translateTerm(args(0))
      (asString(sym), arg.symbol.sort) match {
        case (p(count), BVSort(bits)) => {
          val sort = BVSort(count.toInt+bits)
          val value = BitVectorTheory.BVZeroExtendFactory(count.toInt)(sort)
          uppsat.ast.AST(value, List(arg))
        }
      }
    }


    // TODO: Do we want to check that argumentsort >= end-start > 0?
    case _ if ("extract".r.findFirstIn(asString(sym)).isDefined) => {
       val p = "extract_(\\d+)_(\\d+)".r
       checkArgs("sign_extend", 1, args)
       val arg = translateTerm(args(0))
       (asString(sym)) match {
         case p(start, end) => {
           val sort = BVSort(start.toInt - end.toInt + 1)
           val value = BitVectorTheory.BVExtractFactory(start.toInt, end.toInt)(sort)
           uppsat.ast.AST(value, List(arg))
         }
       }
     }

    case PlainSymbol("bvnot") => {
      checkArgs("bvnot", 1, args)
      bvNot(translateTerm(args(0)))
    }

    case PlainSymbol("bvmul") => {
      checkArgs("bvand", 2, args)
      bvMul(translateTerm(args(0)), translateTerm(args(1)))
    }

    case PlainSymbol("bvashr") => {
      checkArgs("bvashr", 2, args)
      bvAshr(translateTerm(args(0)), translateTerm(args(1)))
    }

    case PlainSymbol("bvand") => {
      checkArgs("bvand", 2, args)
      bvAnd(translateTerm(args(0)), translateTerm(args(1)))
    }

    case PlainSymbol("bvor") => {
      checkArgs("bvor", 2, args)
      bvOr(translateTerm(args(0)), translateTerm(args(1)))
    }

    case PlainSymbol("bvxor") => {
      checkArgs("bvxor", 2, args)
      bvXor(translateTerm(args(0)), translateTerm(args(1)))
    }


    case PlainSymbol("bvslt") => {
      checkArgs("bvslt", 2, args)
      bvLessThan(translateTerm(args(0)), translateTerm(args(1)))
    }

    case PlainSymbol("concat") => {
      checkArgs("concat", 2, args)
      val l = translateTerm(args(0))
      val r = translateTerm(args(1))
      (l.symbol.sort, r.symbol.sort) match {
        case (BVSort(bits1), BVSort(bits2)) => {
          val sort = BVSort(bits1 + bits2)
          val value = BitVectorTheory.BVConcatFactory(sort)
          uppsat.ast.AST(value, List(l, r))
        }
        case (lsort, rsort) => throw new Exception(s"concat with non-BVSort: ${lsort}, ${rsort}")
      }
    }



    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => {
      // TODO: We should maybe not use strings as IDs?
      val fullname = asString(id)
      val name = fixName(fullname)
      (myEnv.findSymbol(name), myEnv.findDefinition(name)) match {
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
