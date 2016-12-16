package uppsat.parser

import uppsat.theory.IntegerTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.BooleanTheory._

import smtlib._
import smtlib.Absyn._
import java.io._
import scala.collection.JavaConversions._

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

  abstract class MyExpression
  abstract class MyFormula extends MyExpression
  abstract class MyTerm extends MyExpression
  case class MyTermITE(str1 : String, str2: String, str3 : String) extends MyTerm
  case class MyFunApp(str1 : String, str2 : List[String]) extends MyTerm
  case class MyConstant(str : String) extends MyTerm
  case class MyIntLit(str : String) extends MyTerm

  case class StrangeFormula(str : String) extends MyFormula

  /// PHILIPPS

  private val printer = new PrettyPrinterNonStatic

  abstract class SMTType
  case object SMTBool extends SMTType
  case object SMTInteger extends SMTType
  case object SMTUnknown extends SMTType
  case class  SMTArray(arguments : List[SMTType],
                       result : SMTType) extends SMTType

  private def parse(script : Script) : Unit =
    for (cmd <- script.listcommand_) parse(cmd)

  // Should we output on success?
  private var printSuccess = true
  // Should we give warning for decl-const (Which is not SMT2)?
  private var declareConstWarning = false

  // "Our" environment
  var myEnv = new Environment
  private def success : Unit = {
    if (printSuccess)
      println("success")
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
//      sanitise(s.normalsymbolt_)
      s.normalsymbolt_
    case s : QuotedSymbol =>
//      sanitise(s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1))
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

  object IBinJunctor extends Enumeration {
    val And, Or, Eqv, EqualitySign = Value
  }

  protected def checkArgNum(op : String, expected : Int, args : Seq[Term]) : Unit =
    if (expected != args.size)
      throw new Exception(
          "Operator \"" + op +
          "\" is applied to a wrong number of arguments: " +
          ((for (a <- args) yield (printer print a)) mkString ", "))

 // TODO: What does this do?
//  protected def asFormula(expr : (MyExpression, SMTType)) : uppsat.ast.AST = expr match {
//    case (expr : MyFormula, SMTBool) =>
//      expr
//    // case (expr : MyTerm, SMTBool) =>
//    case (expr : MyTerm, _) =>
//      // then we assume that an integer encoding of boolean values was chosen
//      StrangeFormula(expr.toString())
//    // IIntFormula(IIntRelation.EqZero, expr)
//    case (expr, _) =>
//      println(expr.getClass)
//      throw new Exception(
//        "Expected a formula, not " + expr)
//  }

  protected def translateTerm(t : Term, polarity : Int)
      : uppsat.ast.AST = t match {
    case t : smtlib.Absyn.ConstantTerm =>
      translateSpecConstant(t.specconstant_)
    case t : FunctionTerm =>
      symApp(t.symbolref_, t.listterm_, polarity)
    case t : NullaryTerm =>
      symApp(t.symbolref_, List(), polarity)     
    case _ => throw new Exception("Unknown term: " + t.toString())

    // case t : QuantifierTerm =>
    //   translateQuantifier(t, polarity)
      
    // case t : AnnotationTerm => {
    //   val triggers = for (annot <- t.listannotation_;
    //     a = annot.asInstanceOf[AttrAnnotation];
    //     if (a.annotattribute_ == ":pattern")) yield {
    //     a.attrparam_ match {
    //       case p : SomeAttrParam => p.sexpr_ match {
    //         case e : ParenSExpr =>
    //           for (expr <- e.listsexpr_.toList;
    //             transTriggers = {
    //               try { List(translateTrigger(expr)) }
    //               catch { case _ : TranslationException |
    //                 _ : Environment.EnvironmentException => {
    //                   warn("could not parse trigger " +
    //                     (printer print expr) +
    //                     ", ignoring")
    //                   List()
    //                 } }
    //             };
    //             t <- transTriggers) yield t
    //         case _ =>
    //           throw new Parser2InputAbsy.TranslationException(
    //             "Expected list of patterns after \":pattern\"")
    //       }
    //       case _ : NoAttrParam =>
    //         throw new Parser2InputAbsy.TranslationException(
    //           "Expected trigger patterns after \":pattern\"")
    //     }
    //   }

    //   val baseExpr =
    //     if (genInterpolants) {
    //       val names = for (annot <- t.listannotation_;
    //         a = annot.asInstanceOf[AttrAnnotation];
    //         if (a.annotattribute_ == ":named")) yield {
    //         a.attrparam_ match {
    //           case p : SomeAttrParam => p.sexpr_ match {
    //             case e : SymbolSExpr =>
    //               printer print e
    //             case _ =>
    //               throw new Parser2InputAbsy.TranslationException(
    //                 "Expected name after \":named\"")
    //           }
    //           case _ : NoAttrParam =>
    //             throw new Parser2InputAbsy.TranslationException(
    //               "Expected name after \":named\"")
    //         }
    //       }
          
    //       translateTerm(t.term_, polarity) match {
    //         case p@(expr, SMTBool) =>
    //           ((asFormula(p) /: names) {
    //             case (res, name) => INamedPart(env lookupPartName name, res)
    //           }, SMTBool)
    //         case p =>
    //           // currently names for terms are ignored
    //           p
    //       }
    //     } else {
    //       translateTerm(t.term_, polarity)
    //     }

    //   if (triggers.isEmpty)
    //     baseExpr
    //   else
    //     ((asFormula(baseExpr) /: triggers) {
    //       case (res, trigger) => ITrigger(ITrigger.extractTerms(trigger), res)
    //     }, SMTBool)
    // }
      
    // case t : LetTerm =>
    //   translateLet(t, polarity)
  }

  // TODO: Int => ItdealInt/Rat=> IdealRat
  protected def translateSpecConstant(c : SpecConstant)
      : uppsat.ast.AST = {
    c match {
      // TODO: What is numconstant? Also FP?
    case c : NumConstant => {
      uppsat.ast.Leaf(uppsat.theory.IntegerTheory.IntLiteral(c.numeral_.toInt))
    }
//    case c : HexConstant =>
//      (MyIntLit(c.hexadecimal_ substring (2, 16)), SMTInteger)
//    case c : BinConstant =>
//      (MyIntLit(c.binary_ substring (2, 2)), SMTInteger)
    case  c => {
      throw new Exception("Unknown SpecConstant: " + c + " (" + c.getClass +")")
    }

    // case c : RatConstant => {
    //   val v = c.rational_
    //   (v, SMTInteger)
    //   // if (v.denom.isOne) {
    //   //   warn("mapping rational literal " + c.rational_ + " to an integer literal")
    //   //   (v.num, SMTInteger)
    //   // } else {
    //   //   warn("mapping rational literal " + c.rational_ + " to an integer constant")
    //   //   val const = new ConstantTerm("rat_" + c.rational_)
    //   //   // addConstant(const, SMTInteger)
    //   //   (const, SMTInteger)
    //   // }
    // }
    }
  }

  // private def importProverSymbol(name : String,
  //                                args : Seq[SMTType],
  //                                res : SMTType) : Boolean =
  //   incremental &&
  //   ((reusedSymbols get name) match {
  //      case None =>
  //        false
  //      case Some(c : ConstantTerm) if (args.isEmpty) => {
  //        env.addConstant(c, Environment.NullaryFunction, res)
  //        true
  //      }
  //      case Some(f : IFunction) if (args.size == f.arity) => {
  //        env.addFunction(f, SMTFunctionType(args.toList, res))
  //        true
  //      }
  //      case Some(p : Predicate) if (args.size == p.arity && res == SMTBool) => {
  //        env.addPredicate(p, ())
  //        true
  //      }
  //      case Some(_) => {
  //        warn("inconsistent definition of symbol " + name)
  //        false
  //      }
  //    })

  private def parse(cmd : Command) : Unit = cmd match {

    case cmd : SetLogicCommand => {
      // just ignore for the time being
      success
    }

      //////////////////////////////////////////////////////////////////////////

    case cmd : SetOptionCommand => {
      // TODO: Do we have to handle SetOptionCommand?
      success
      // val annot = cmd.optionc_.asInstanceOf[Option]
      //   .annotation_.asInstanceOf[AttrAnnotation]

      // val handled =
      //   handleBooleanAnnot(":print-success", annot) {
      //     value => printSuccess = value
      //   } ||
      // handleBooleanAnnot(":produce-models", annot) {
      //   value => // nothing
      // } ||
      // handleBooleanAnnot(":boolean-functions-as-predicates", annot) {
      //   value => booleanFunctionsAsPredicates = value
      // } ||
      // handleBooleanAnnot(":inline-let", annot) {
      //   value => inlineLetExpressions = value
      // } ||
      // handleBooleanAnnot(":inline-definitions", annot) {
      //   value => inlineDefinedFuns = value
      // } ||
      // handleBooleanAnnot(":totality-axiom", annot) {
      //   value => totalityAxiom = value
      // } ||
      // handleBooleanAnnot(":functionality-axiom", annot) {
      //   value => functionalityAxiom = value
      // } ||
      // handleBooleanAnnot(":produce-interpolants", annot) {
      //   value => {
      //     genInterpolants = value
      //     if (incremental)
      //       prover.setConstructProofs(value)
      //   }
      // } ||
      // handleNumAnnot(":timeout-per", annot) {
      //   value => timeoutPer = (value min IdealInt(Int.MaxValue)).intValue
      // }

      // if (handled) {
      //   success
      // } else {
      //   if (incremental)
      //     unsupported
      //   else
      //     warn("ignoring option " + annot.annotattribute_)
      // }
    }

  //     //////////////////////////////////////////////////////////////////////////
      
  //   case cmd : SetInfoCommand =>
  //     success

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : SortDeclCommand if (incremental) =>
  //     unsupported

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : SortDefCommand => {
  //     if (!cmd.listsymbol_.isEmpty)
  //       throw new Parser2InputAbsy.TranslationException(
  //         "Currently only define-sort with arity 0 is supported")
  //     sortDefs = sortDefs + (asString(cmd.symbol_) -> translateSort(cmd.sort_))
  //     success
  //   }

  //     //////////////////////////////////////////////////////////////////////////
      
    case cmd : FunctionDeclCommand => {
      // Functions are always declared to have integer inputs and outputs
      val name = asString(cmd.symbol_)
      cmd.mesorts_ match {
        case _ : NoSorts => {
          val res = translateSort(cmd.sort_)          
          val symbol = res match {
            case IntegerSort => new uppsat.theory.IntegerTheory.IntVar(name)
            case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
            case fp : FPSort => new uppsat.theory.FloatingPointTheory.FPVar(name, fp)
          }

          myEnv.addSymbol(name, symbol)
        }
        case _ => throw new Exception("Function Declaration with arguments!")
//        case sorts : SomeSorts =>
//          for (s <- sorts.listsort_) yield translateSort(s)
      }


      // TODO: How do we represent function applications?
      // ensureEnvironmentCopy

      // if (!importProverSymbol(name, args, res)) {
      //   if (args.length > 0) {
      //     if (!booleanFunctionsAsPredicates || res != SMTBool) {
      //       // use a real function
      //       val f = new IFunction(name, args.length,
      //         !totalityAxiom, !functionalityAxiom)
      //       env.addFunction(f, SMTFunctionType(args.toList, res))
      //       if (incremental)
      //         prover.addFunction(f,
      //           if (functionalityAxiom)
      //             SimpleAPI.FunctionalityMode.Full
      //           else
      //             SimpleAPI.FunctionalityMode.None)
      //     } else {
      //       // use a predicate
      //       val p = new Predicate(name, args.length)
      //       env.addPredicate(p, ())
      //       if (incremental)
      //         prover.addRelation(p)
      //     }
      //   } else if (res != SMTBool) {
      //     // use a constant
      //     addConstant(new ConstantTerm(name), res)
      //   } else {
      //     // use a nullary predicate (propositional variable)
      //     val p = new Predicate(name, 0)
      //     env.addPredicate(p, ())
      //     if (incremental)
      //       prover.addRelation(p)
      //   }
      // }

      success
    }

  //     //////////////////////////////////////////////////////////////////////////

    case cmd : ConstDeclCommand => {
      if (!declareConstWarning) {
        warn("accepting command declare-const, which is not SMT-LIB 2")
        declareConstWarning = true
      }

      val name = asString(cmd.symbol_)
      val res = translateSort(cmd.sort_)

      val symbol = 
        res match {
          case IntegerSort => new uppsat.theory.IntegerTheory.IntVar(name)
          case BooleanSort => new uppsat.theory.BooleanTheory.BoolVar(name)
          case sort => throw new Exception("ast._.sort not handled: " + sort)
        }

      println("Adding2: (" + name + ", " + symbol + ")")
      myEnv.addSymbol(name, symbol)
      // ensureEnvironmentCopy


      // TODO: Do this!
      // if (!importProverSymbol(name, List(), res)) {
      //   if (res != SMTBool) {
      //     // use a constant
      //     addConstant(new ConstantTerm(name), res)
      //   } else {
      //     // use a nullary predicate (propositional variable)
      //     val p = new Predicate(name, 0)
      //     env.addPredicate(p, ())
      //     if (incremental)
      //       prover.addRelation(p)
      //   }
      // }

      success
    }

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : FunctionDefCommand => {
  //     // Functions are always declared to have integer inputs and outputs
  //     val name = asString(cmd.symbol_)
  //     val args : Seq[SMTType] =
  //       for (sortedVar <- cmd.listesortedvarc_)
  //       yield translateSort(sortedVar.asInstanceOf[ESortedVar].sort_)
  //     val argNum = pushVariables(cmd.listesortedvarc_)
  //     val resType = translateSort(cmd.sort_)
      
  //     // parse the definition of the function
  //     val body@(_, bodyType) = translateTerm(cmd.term_, 0)

  //     if (bodyType != resType)
  //       throw new Parser2InputAbsy.TranslationException(
  //         "Body of function definition has wrong type")

  //     // pop the variables from the environment
  //     for (_ <- PlainRange(argNum)) env.popVar

  //     // use a real function
  //     val f = new IFunction(name, argNum, true, true)
  //     env.addFunction(f, SMTFunctionType(args.toList, resType))
  //     if (incremental)
  //       prover.addFunction(f, SimpleAPI.FunctionalityMode.NoUnification)
      
  //     if (inlineDefinedFuns) {
  //       functionDefs = functionDefs + (f -> body)
  //     } else {
  //       // set up a defining equation and formula
  //       val lhs = IFunApp(f, for (i <- 1 to argNum) yield v(argNum - i))
  //       val matrix = ITrigger(List(lhs), lhs === asTerm(body))
  //       addAxiom(quan(Array.fill(argNum){Quantifier.ALL}, matrix))
  //     }

  //     success
  //   }

  //     //////////////////////////////////////////////////////////////////////////
      
  //   case cmd : PushCommand => {
  //     for (_ <- 0 until cmd.numeral_.toInt)
  //       push
  //     success
  //   }

  //   case cmd : PopCommand => {
  //     for (_ <- 0 until cmd.numeral_.toInt)
  //       pop
  //     success
  //   }

  //     //////////////////////////////////////////////////////////////////////////
      
    case cmd : AssertCommand => {
      val t = translateTerm(cmd.term_, -1)
      myEnv.addAssumption(t)

      // if (incremental && !justStoreAssertions) {
      //   if (genInterpolants) {
      //     PartExtractor(f, false) match {
      //       case List(INamedPart(PartName.NO_NAME, g)) => {
      //         // generate consecutive partition numbers
      //         prover setPartitionNumber nextPartitionNumber
      //         nextPartitionNumber = nextPartitionNumber + 1
      //         prover addAssertion PartNameEliminator(g)
      //       }
      //       case parts =>
      //         for (INamedPart(name, g) <- parts) {
      //           prover setPartitionNumber getPartNameIndexFor(name)
      //           prover addAssertion PartNameEliminator(g)
      //         }
      //     }
      //   } else {
      //     prover addAssertion f
      //   }
      // } else {
      //   assumptions += f
      // }

      success
    }

  //     //////////////////////////////////////////////////////////////////////////
    case cmd : CheckSatCommand => {
      myEnv.print
      val formula = myEnv.assumptions.head
      val translator = new uppsat.solver.SMTTranslator(uppsat.theory.IntegerTheory)
      val approximation = uppsat.approximation.IntApproximation
      println("CHECK SAT")
      uppsat.ApproximationSolver.loop(formula, translator, approximation)
      success
    }
  //   case cmd : CheckSatCommand => if (incremental) try {
  //     var res = prover checkSat false
  //     val startTime = System.currentTimeMillis

  //     while (res == SimpleAPI.ProverStatus.Running) {
  //       if (timeoutChecker()) {
  //         println("unknown")
  //         lastReasonUnknown = "timeout"
  //         Console.err.println("Global timeout, stopping solver")
  //         prover.stop
  //         throw ExitException
  //       }
  //       if ((System.currentTimeMillis - startTime).toInt > timeoutPer)
  //         prover.stop
  //       res = prover.getStatus(100)
  //     }
      
  //     res match {
  //       case SimpleAPI.ProverStatus.Sat |
  //           SimpleAPI.ProverStatus.Invalid =>
  //         println("sat")
  //       case SimpleAPI.ProverStatus.Unsat |
  //           SimpleAPI.ProverStatus.Valid =>
  //         println("unsat")
  //       case SimpleAPI.ProverStatus.Unknown => {
  //         println("unknown")
  //         lastReasonUnknown = "timeout"
  //       }
  //       case SimpleAPI.ProverStatus.Inconclusive => {
  //         println("unknown")
  //         lastReasonUnknown = "incomplete"
  //       }
  //       case _ =>
  //         error("unexpected prover result")
  //     }
  //   } catch {
  //     case e : SimpleAPI.SimpleAPIException =>
  //       error(e.getMessage)
  //   }

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetAssertionsCommand =>
  //     error("get-assertions not supported")

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetValueCommand => if (checkIncrementalWarn("get-value")) {
  //     prover.getStatus(false) match {
  //       case SimpleAPI.ProverStatus.Sat |
  //           SimpleAPI.ProverStatus.Invalid |
  //           SimpleAPI.ProverStatus.Inconclusive => try {
  //             val expressions = cmd.listterm_.toList

  //             var unsupportedType = false
  //             val values = prover.withTimeout(timeoutPer) {
  //               for (expr <- expressions) yield
  //                 translateTerm(expr, 0) match {
  //                   case p@(_, SMTBool) =>
  //                     (prover eval asFormula(p)).toString
  //                   case p@(_, SMTInteger) =>
  //                     SMTLineariser toSMTExpr (prover eval asTerm(p))
  //                   case (_, _) => {
  //                     unsupportedType = true
  //                     ""
  //                   }
  //                 }
  //             }
              
  //             if (unsupportedType) {
  //               error("cannot print values of this type yet")
  //             } else {
  //               println("(" +
  //                 (for ((e, v) <- expressions.iterator zip values.iterator)
  //                 yield ("(" + (printer print e) + " " + v + ")")).mkString(" ") +
  //                 ")")
  //             }
  //           } catch {
  //             case SimpleAPI.TimeoutException =>
  //               error("timeout when constructing full model")
  //             case SimpleAPI.NoModelException =>
  //               error("no model available")
  //           }

  //       case _ =>
  //         error("no model available")
  //     }
  //   }

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetProofCommand =>
  //     error("get-proof not supported")

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetUnsatCoreCommand =>
  //     error("get-unsat-core not supported")

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetAssignmentCommand =>
  //     error("get-assignment not supported")

  //     //////////////////////////////////////////////////////////////////////////

     case cmd : GetModelCommand => {  
       // TODO: What do we do with get-model statements?
       println("(get-model) ignored!")
       //throw new Exception("get-model in smt-file")
     }

  //     prover.getStatus(false) match {
  //       case SimpleAPI.ProverStatus.Sat |
  //           SimpleAPI.ProverStatus.Invalid |
  //           SimpleAPI.ProverStatus.Inconclusive => try {
  //             val model = prover.withTimeout(timeoutPer) {
  //               prover.partialModel
  //             }

  //             for ((SimpleAPI.ConstantLoc(c), SimpleAPI.IntValue(value)) <-
  //               model.interpretation.iterator)
  //               println("(define-fun " + (SMTLineariser quoteIdentifier c.name) +
  //                 " () Int " + (SMTLineariser toSMTExpr value) + ")")
  //             for ((SimpleAPI.PredicateLoc(p, Seq()), SimpleAPI.BoolValue(value)) <-
  //               model.interpretation.iterator)
  //               println("(define-fun " + (SMTLineariser quoteIdentifier p.name) +
  //                 " () Bool " + value + ")")

  //             /*
  //              val funValues =
  //              (for ((SimpleAPI.IntFunctionLoc(f, args), value) <-
  //              model.interpretation.iterator)
  //              yield (f, args, value)).toSeq.groupBy(_._1)
  //              for ((f, triplets) <- funValues) {
  //              print("(define-fun " + f.name + " (" +
  //              (for (i <- 0 until f.arity) yield ("x" + i + " Int")).mkString(" ") +
  //              ") Int ")
  //              }
  //              */
  //           } catch {
  //             case SimpleAPI.TimeoutException =>
  //               error("timeout when constructing full model")
  //             case SimpleAPI.NoModelException =>
  //               error("no model available")
  //           }

  //       case _ =>
  //         error("no model available")
  //     }
  //   }

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : GetInterpolantsCommand =>
  //     if (incremental) {
  //       if (genInterpolants) prover.getStatus(false) match {
  //         case SimpleAPI.ProverStatus.Unsat |
  //             SimpleAPI.ProverStatus.Valid => {

  //               try { prover.withTimeout(timeoutPer) {
  //                 if (cmd.listsexpr_.isEmpty) {

  //                   val interpolantSpecs =
  //                     for (i <- 0 until nextPartitionNumber) yield Set(i)
  //                   val interpolants = prover.getInterpolants(interpolantSpecs)

  //                   print("(")
  //                   var sep = ""
  //                   for (interpolant <- prover.getInterpolants(interpolantSpecs)) {
  //                     print(sep)
  //                     sep = "\n"
  //                     smtLinearise(interpolant)
  //                   }
  //                   println(")")

  //                 } else translateTreeInterpolantSpec(cmd.listsexpr_) match {

  //                   case List(tree) => {
  //                     val allMentionedNames =
  //                       (for (t <- tree.iterator; n <- t.iterator) yield n).toSet
  //                     val remainingNames =
  //                       ((0 until nextPartitionNumber).iterator filterNot
  //                         allMentionedNames).toList

  //                     val finalTree =
  //                       if (!remainingNames.isEmpty) {
  //                         warn("not all asserted formulas are mentioned in interpolant specification, " +
  //                           "putting remaining formulas in the last/root partition")
  //                         Tree(tree.d ++ remainingNames, tree.children)
  //                       } else {
  //                         tree
  //                       }

  //                     val interpolants =
  //                       prover.getTreeInterpolant(finalTree,
  //                         (timeoutPer / tree.size) min 3000)

  //                     print("(")
  //                     var sep = ""
  //                     for (t <- interpolants.children) t foreachPostOrder { f =>
  //                       print(sep)
  //                       sep = "\n"
  //                       smtLinearise(f)
  //                     }
  //                     println(")")
  //                   }

  //                   case _ =>
  //                     error("could not parse interpolant specification")
  //                 }
  //               } } catch {
  //                 case SimpleAPI.TimeoutException =>
  //                   error("timeout while computing interpolants")
  //               }
  //               /*
  //                Old code that only works for sequence interpolants
  //                for (p <- cmd.listsexpr_.toList) yield p match {
  //                case p : SymbolSExpr =>
  //                Set(partNameIndexes(
  //                env.lookupPartName(printer print p.symbol_)))
  //                case p : ParenSExpr
  //                if (!p.listsexpr_.isEmpty &&
  //                (printer print p.listsexpr_.head) == "and") => {
  //                val it = p.listsexpr_.iterator
  //                it.next
  //                (for (s <- it)
  //                yield partNameIndexes(
  //                env.lookupPartName(printer print s))).toSet
  //                }
  //                case p =>
  //                throw new Parser2InputAbsy.TranslationException(
  //                "Could not parse interpolation partition: " +
  //                (printer print p))
  //                }
  //                */

  //             }

  //         case _ =>
  //           error("no proof available")
  //       } else {
  //         error(":produce-interpolants has to be set before get-interpolants")
  //       }
  //     } else {
  //       genInterpolants = true
  //     }
      
  //     //////////////////////////////////////////////////////////////////////////
      
  //   case cmd : GetInfoCommand => if (checkIncrementalWarn("get-info"))
  //     cmd.annotattribute_ match {
  //       case ":authors" => {
  //         println("(:authors \"")
  //         CmdlMain.printGreeting
  //         println("\n\")")
  //       }
  //       case ":name" =>
  //         println("(:name \"Princess\")")
  //       case ":version" =>
  //         println("(:version \"" + CmdlMain.version + "\")")
  //       case ":error-behavior" =>
  //         println("(:error-behavior \"immediate-exit\")")
  //       case ":interpolation-method" =>
  //         println("(:interpolation-method \"tree\")")
  //       case ":reason-unknown" =>
  //         println("(:reason-unknown " + lastReasonUnknown + ")")
  //     }
      
  //     //////////////////////////////////////////////////////////////////////////
      
  //   case cmd : GetOptionCommand => if (checkIncrementalWarn("get-option")) {
  //     unsupported
  //   }
      
  //     //////////////////////////////////////////////////////////////////////////
      
  //   case cmd : EchoCommand => if (checkIncrementalWarn("echo")) {
  //     if (!echoWarning) {
  //       warn("accepting command echo, which is not SMT-LIB 2")
  //       echoWarning = true
  //     }
  //     val str = cmd.smtstring_
  //     println(str.substring(1, str.size - 1))
  //   }

  //     //////////////////////////////////////////////////////////////////////////

  //   case cmd : ResetCommand => if (checkIncrementalWarn("reset")) {
  //     reset
  //   }

  //     //////////////////////////////////////////////////////////////////////////

    case cmd : ExitCommand => success
    // case cmd : ExitCommand => if (checkIncrementalWarn("exit")) {
    //   throw ExitException
    // }

  //     //////////////////////////////////////////////////////////////////////////

  //   case _ : EmptyCommand =>
  //     // command to be ignored

  //     //////////////////////////////////////////////////////////////////////////

  //   case _ =>
  //     warn("ignoring " + (printer print cmd))
  }

  //////////////////////////////////////////////////////////////////////////////

  //protected def translateSort(s : Sort) : SMTType = s match {
  protected def translateSort(s : Sort) : uppsat.ast.Sort = {
    val fpPattern = "FloatingPoint\\_(\\d+)\\_(\\d+)".r
    s match {
    case s : IdentSort => asString(s.identifier_) match {
      case "Int" => IntegerSort
      case "Bool" => BooleanSort
      // case id if (sortDefs contains id) => sortDefs(id)
      case fpPattern(eBits, sBits) => uppsat.theory.FloatingPointTheory.FPSortFactory(List(eBits.toInt, sBits.toInt))
      case id => {
        println("Unknown sort: " + asString(s.identifier_))
        throw new Exception("Unknown sort...")
      }
    }
    // case s : CompositeSort => asString(s.identifier_) match {
    //   case "Array" => {
    //     val args =
    //       for (t <- s.listsort_.toList) yield translateSort(t)
    //     if (args.size < 2)
    //       throw new Parser2InputAbsy.TranslationException(
    //         "Expected at least two sort arguments in " + (printer print s))
    //     SMTArray(args.init, args.last)
    //   }
    //   case id => {
    //     warn("treating sort " + (printer print s) + " as Int")
    //     SMTInteger
    //   }
    // }
    }
  }

  // //////////////////////////////////////////////////////////////////////////////



  // //////////////////////////////////////////////////////////////////////////////

  // // add bound variables to the environment and record their number
  // private def pushVariables(vars : smtlib.Absyn.ListSortedVariableC) : Int = {
  //   var quantNum : Int = 0
    
  //   for (binder <- vars) binder match {
  //     case binder : SortedVariable => {
  //       pushVar(binder.sort_, binder.symbol_)
  //       quantNum = quantNum + 1
  //     }
  //   }
    
  //   quantNum
  // }

  // private def pushVariables(vars : smtlib.Absyn.ListESortedVarC) : Int = {
  //   var quantNum : Int = 0
    
  //   for (binder <- vars) binder match {
  //     case binder : ESortedVar => {
  //       pushVar(binder.sort_, binder.symbol_)
  //       quantNum = quantNum + 1
  //     }
  //   }
    
  //   quantNum
  // }

  // private def pushVar(bsort : Sort, bsym : Symbol) : Unit = {
  //   ensureEnvironmentCopy
  //   env.pushVar(asString(bsym), BoundVariable(translateSort(bsort)))
  // }
  
  // private def translateQuantifier(t : QuantifierTerm, polarity : Int)
  //     : (IExpression, SMTType) = {
  //   val quant : Quantifier = t.quantifier_ match {
  //     case _ : AllQuantifier => Quantifier.ALL
  //     case _ : ExQuantifier => Quantifier.EX
  //   }

  //   val quantNum = pushVariables(t.listsortedvariablec_)
    
  //   val body = asFormula(translateTerm(t.term_, polarity))

  //   // we might need guards 0 <= x <= 1 for quantifiers ranging over booleans
  //   val guard = connect(
  //     for (binderC <- t.listsortedvariablec_.iterator;
  //       binder = binderC.asInstanceOf[SortedVariable];
  //       if (translateSort(binder.sort_) == SMTBool)) yield {
  //       (env lookupSym asString(binder.symbol_)) match {
  //         case Environment.Variable(ind, _) => (v(ind) >= 0) & (v(ind) <= 1)
  //         case _ => { // just prevent a compiler warning
  //                     //-BEGIN-ASSERTION-///////////////////////////////////////////////
  //           Debug.assertInt(SMTParser2InputAbsy.AC, false)
  //           //-END-ASSERTION-/////////////////////////////////////////////////
  //           null
  //         }
  //       }
  //     },
  //     IBinJunctor.And)
    
  //   val matrix = guard match {
  //     case IBoolLit(true) =>
  //       body
  //     case _ => {
  //       // we need to insert the guard underneath possible triggers
  //       def insertGuard(f : IFormula) : IFormula = f match {
  //         case ITrigger(pats, subF) =>
  //           ITrigger(pats, insertGuard(subF))
  //         case _ => quant match {
  //           case Quantifier.ALL => guard ===> f
  //           case Quantifier.EX => guard &&& f
  //         }
  //       }
        
  //       insertGuard(body)
  //     }
  //   }
    
  //   val res = quan(Array.fill(quantNum){quant}, matrix)

  //   // pop the variables from the environment
  //   for (_ <- PlainRange(quantNum)) env.popVar
    
  //   (res, SMTBool)
  // }
  
  // //////////////////////////////////////////////////////////////////////////////

  // private var letVarCounter = 0
  
  // private def letVarName(base : String) = {
  //   val res = base + "_" + letVarCounter
  //   letVarCounter = letVarCounter + 1
  //   res
  // }
  
  // /**
  //   * If t is an integer term, let expression in positive position:
  //   *   (let ((v t)) s)
  //   *   ->
  //   *   \forall int v; (v=t -> s)
  //   * 
  //   * If t is a formula, let expression in positive position:
  //   *   (let ((v t)) s)
  //   *   ->
  //   *   \forall int v; ((t <-> v=0) -> s)
  //   *   
  //   * TODO: possible optimisation: use implications instead of <->, depending
  //   * on the polarity of occurrences of v
  //   */
  // private def translateLet(t : LetTerm, polarity : Int)
  //     : (IExpression, SMTType) = {
  //   val bindings = for (b <- t.listbindingc_) yield {
  //     val binding = b.asInstanceOf[Binding]
  //     val (boundTerm, boundType) = translateTerm(binding.term_, 0)
  //     (asString(binding.symbol_), boundType, boundTerm)
  //   }

  //   ensureEnvironmentCopy

  //   if (env existsVar (_.isInstanceOf[BoundVariable])) {
  //     // we are underneath a real quantifier, so have to introduce quantifiers
  //     // for this let expression, or directly substitute
      
  //     for ((v, t, _) <- bindings) env.pushVar(v, BoundVariable(t))

  //     val wholeBody@(body, bodyType) = translateTerm(t.term_, polarity)
      
  //     for (_ <- bindings) env.popVar

  //     //////////////////////////////////////////////////////////////////////////
      
  //     if (inlineLetExpressions) {
  //       // then we directly inline the bound formulae and terms
        
  //       val subst = for ((_, t, s) <- bindings.toList.reverse) yield asTerm((s, t))
  //       (LetInlineVisitor.visit(body, (subst, -bindings.size)), bodyType)
  //     } else {
  //       val definingEqs =
  //         connect(for (((_, t, s), num) <- bindings.iterator.zipWithIndex) yield {
  //           val shiftedS = VariableShiftVisitor(s, 0, bindings.size)
  //           val bv = v(bindings.length - num - 1)
  //           t match {
  //             case SMTBool    =>
  //               IFormulaITE(asFormula((shiftedS, t)),
  //                 IIntFormula(IIntRelation.EqZero, bv),
  //                 IIntFormula(IIntRelation.EqZero, bv + i(-1)))
  //             case _ =>
  //               asTerm((shiftedS, t)) === bv
  //           }}, IBinJunctor.And)
        
  //       bodyType match {
  //         case SMTBool =>
  //           (if (polarity > 0)
  //             quan(Array.fill(bindings.length){Quantifier.ALL},
  //               definingEqs ==> asFormula(wholeBody))
  //           else
  //             quan(Array.fill(bindings.length){Quantifier.EX},
  //               definingEqs &&& asFormula(wholeBody)),
  //             SMTBool)
  //       }
  //     }
      
  //   } else {
  //     // we introduce a boolean or integer variables to encode this let expression

  //     for ((name, t, s) <- bindings)
  //       // directly substitute small expressions, unless the user
  //       // has chosen otherwise
  //       if (inlineLetExpressions && SizeVisitor(s) <= 1000) {
  //         env.pushVar(name, SubstExpression(s, t))
  //       } else addAxiom(t match {
  //         case SMTBool => {
  //           val f = new IFunction(letVarName(name), 1, true, false)
  //           env.addFunction(f, SMTFunctionType(List(SMTInteger), SMTInteger))
  //           if (incremental)
  //             prover.addFunction(f)
  //           env.pushVar(name, SubstExpression(all(eqZero(v(0)) ==> eqZero(f(v(0)))),
  //             SMTBool))
  //           all(ITrigger(List(f(v(0))),
  //             eqZero(v(0)) ==>
  //               ((eqZero(f(v(0))) & asFormula((s, t))) |
  //                 ((f(v(0)) === 1) & !asFormula((s, t))))))
  //         }
  //         case exprType => {
  //           val c = new ConstantTerm(letVarName(name))
  //           addConstant(c, exprType)
  //           env.pushVar(name, SubstExpression(c, exprType))
  //           c === asTerm((s, t))
  //         }
  //       })
      
  //     /*
  //      val definingEqs = connect(
  //      for ((v, t, s) <- bindings.iterator) yield
  //      if (SizeVisitor(s) <= 20) {
  //      env.pushVar(v, SubstExpression(s, t))
  //      i(true)
  //      } else t match {
  //      case SMTBool => {
  //      val p = new Predicate(letVarName(v), 0)
  //      env.addPredicate(p, ())
  //      env.pushVar(v, SubstExpression(p(), SMTBool))
  //      asFormula((s, t)) <=> p()
  //      }
  //      case SMTInteger => {
  //      val c = new ConstantTerm(letVarName(v))
  //      env.addConstant(c, Environment.NullaryFunction, ())
  //      env.pushVar(v, SubstExpression(c, SMTInteger))
  //      asTerm((s, t)) === c
  //      }
  //      }, IBinJunctor.And)
  //      */
      
  //     val wholeBody = translateTerm(t.term_, polarity)
      
  //     /*      val definingEqs =
  //      connect(for ((v, t, s) <- bindings.reverseIterator) yield {
  //      (env lookupSym v) match {
  //      case Environment.Variable(_, IntConstant(c)) =>
  //      asTerm((s, t)) === c
  //      case Environment.Variable(_, BooleanConstant(p)) =>
  //      asFormula((s, t)) <=> p()
  //      }}, IBinJunctor.And) */
      
  //     for (_ <- bindings) env.popVar

  //     wholeBody
  //   }
  // }
  
  // //////////////////////////////////////////////////////////////////////////////

  // private var tildeWarning = false
  
  protected def symApp(sym : SymbolRef, args : Seq[Term], polarity : Int)
      : uppsat.ast.AST = sym match {
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded connectives of formulae
    
    case PlainSymbol("true") => {
      checkArgNum("true", 0, args)
      uppsat.ast.Leaf(BoolTrue)
    }
    case PlainSymbol("false") => {
      uppsat.ast.Leaf(BoolFalse)
    }

    // case PlainSymbol("not") => {
    //   checkArgNum("not", 1, args)
    //   (!asFormula(translateTerm(args.head, -polarity)), SMTBool)
    // }
      
    // case PlainSymbol("and") =>
    //   (connect(for (s <- flatten("and", args))
    //   yield asFormula(translateTerm(s, polarity)),
    //     IBinJunctor.And),
    //     SMTBool)
      
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
      if (args.length != 2) {
        throw new Exception("Not two arguments for + ...")
      } else {
        translateTerm(args(0), 0) + translateTerm(args(1), 0)
      }
    }    
    
    
    //   ////////////////////////////////////////////////////////////////////////////
    //   // Hardcoded predicates (which might also operate on booleans)
      
    case PlainSymbol("=") => {
      if (args.length != 2) {
        throw new Exception("Not two arguments for = ...")
      } else {
        val lhs = translateTerm(args(0), 0)
        val rhs = translateTerm(args(1), 0)
        lhs.prettyPrint
        println(rhs)
        translateTerm(args(0), 0) === translateTerm(args(1), 0)
      }
    }
     
    case PlainSymbol("fp.leq") => {
      if (args.length != 2) {
        throw new Exception("Not two arguments for fp.leq ...")
      } else {
        translateTerm(args(0), 0) <= translateTerm(args(1), 0)
      }
    }    
     
      // for (Seq(a, b) <- (transArgs map (asFormula(_))) sliding 2)
      // yield (
      //   // println("transArgs: " + transArgs.mkString(", "))
      //   (if (transArgs forall (_._2 == SMTBool)) {
      //     connect(for (Seq(a, b) <- (transArgs map (asFormula(_))) sliding 2)
      //     yield (a <===> b),
      //       IBinJunctor.And)
      // } else {
      //   val types = (transArgs map (_._2)).toSet
      //   if (types.size > 1)
      //     throw new Parser2InputAbsy.TranslationException(
      //       "Can only compare terms of same type using =")
      //   connect(for (Seq(a, b) <- (transArgs map (asTerm(_))) sliding 2)
      //   yield translateEq(a, b, types.iterator.next, polarity),
      //     IBinJunctor.And)
      // },
      //   SMTBool)
      
    // case PlainSymbol("distinct") => {
    //   val transArgs = for (a <- args) yield translateTerm(a, 0)
    //   (if (transArgs forall (_._2 == SMTBool)) transArgs.length match {
    //     case 0 | 1 => true
    //     case 2 => ~(asFormula(transArgs(0)) <===> asFormula(transArgs(1)))
    //     case _ => false
    //   } else {
    //     val types = (transArgs map (_._2)).toSet
    //     if (types.size > 1)
    //       throw new Parser2InputAbsy.TranslationException(
    //         "Can only compare terms of same type using distinct")
    //     distinct(for (p <- transArgs.iterator) yield asTerm(p))
    //   }, SMTBool)
    // }
      
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
    //   }
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

    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => {
      // TODO: We should maybe not use strings as IDs?
      myEnv.find(asString(id)) match {
        case Some(symbol) => {
          uppsat.ast.Leaf(symbol)
        }
        case None => throw new Exception("Undefined symbol: " + asString(id))
      }
//      println("Bailing out on uniterpreted formula: " + asString(id))
//      unintFunApp(asString(id), sym, args, polarity)
    }
  }

  // private def translateEq(a : ITerm, b : ITerm, t : SMTType,
  //   polarity : Int) : IFormula =
  //   t match {
  //     case SMTArray(argTypes, resType) if (polarity > 0) => {
  //       val arity = argTypes.size
  //       val theory = SimpleArray(arity)
  //       val args = (for (n <- 0 until arity) yield v(n))
  //       val matrix =
  //         translateEq(IFunApp(theory.select,
  //           List(VariableShiftVisitor(a, 0, arity)) ++ args),
  //           IFunApp(theory.select,
  //             List(VariableShiftVisitor(b, 0, arity)) ++ args),
  //           resType, polarity)

  //       quan(for (_ <- 0 until arity) yield Quantifier.ALL, matrix)
  //     }

  //     case SMTBool =>
  //       eqZero(a) <=> eqZero(b)
  //       //        all(all(!((VariableShiftVisitor(a, 0, 2) === v(0)) &
  //       //                 (VariableShiftVisitor(b, 0, 2) === v(1)) &
  //       //                 ((eqZero(v(0)) & (v(1) === 1)) | (eqZero(v(1)) & (v(0) === 1))))))
  //       //                 geqZero(v(0)) & geqZero(v(1)) & (v(0) <= 1) & (v(1) <= 1)) ==>
  //       //                (v(0) === v(1))))

  //     case _ =>
  //       a === b
  //   }

  // TODO: What does this do?
  // GUESS: We are trying to apply "id" to args? What is polarity and sym?
  // UNINTERPRETED function application
  private def unintFunApp(id : String,
    sym : SymbolRef, args : Seq[Term], polarity : Int)
      : uppsat.ast.AST = {
    val funSort = myEnv.lookup(id)
    throw new Exception("Cannot handle uninterpreted function applications")    
//    if (args.length > 0) {
//      val transArgs = args.map(x => translateTerm(x, 0))
//      (MyConstant(id + "(" + transArgs.mkString(", ") + ")"), SMTUnknown)
//    } else {
//      (MyConstant(id), SMTUnknown)
//
//    }
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
  
  // //////////////////////////////////////////////////////////////////////////////
  
  // private def translateTrigger(expr : SExpr) : IExpression = expr match {
    
  //   case expr : ConstantSExpr => translateSpecConstant(expr.specconstant_)._1
      
  //   case expr : SymbolSExpr => (env lookupSym asString(expr.symbol_)) match {
  //     case Environment.Function(fun, _) => {
  //       checkArgNumSExpr(printer print expr.symbol_,
  //         fun.arity, List[SExpr]())
  //       IFunApp(fun, List())
  //     }
  //     case Environment.Predicate(pred, _, _) => {
  //       checkArgNumSExpr(printer print expr.symbol_,
  //         pred.arity, List[SExpr]())
  //       IAtom(pred, List())
  //     }
  //     case Environment.Constant(c, _, _) => c
  //     case Environment.Variable(i, BoundVariable(t)) if (t != SMTBool) => v(i)
  //     case _ =>
  //       throw new Parser2InputAbsy.TranslationException(
  //         "Unexpected symbol in a trigger: " +
  //           (printer print expr.symbol_))
  //   }
      
  //   case expr : ParenSExpr => {
  //     if (expr.listsexpr_.isEmpty)
  //       throw new Parser2InputAbsy.TranslationException(
  //         "Expected a function application, not " + (printer print expr))
      
  //     expr.listsexpr_.head match {
  //       case funExpr : SymbolSExpr => asString(funExpr.symbol_) match {
  //         case "select" =>
  //           IFunApp(SimpleArray(expr.listsexpr_.size - 2).select,
  //             translateSExprTail(expr.listsexpr_))
  //         case "store" =>
  //           IFunApp(SimpleArray(expr.listsexpr_.size - 3).store,
  //             translateSExprTail(expr.listsexpr_))

  //         case funName => (env lookupSym funName) match {
  //           case Environment.Function(fun, _) => {
  //             checkArgNumSExpr(printer print funExpr.symbol_, fun.arity,
  //               expr.listsexpr_.tail)
  //             IFunApp(fun, translateSExprTail(expr.listsexpr_))
  //           }
  //           case Environment.Predicate(pred, _, _) => {
  //             checkArgNumSExpr(printer print funExpr.symbol_, pred.arity,
  //               expr.listsexpr_.tail)
  //             IAtom(pred, translateSExprTail(expr.listsexpr_))
  //           }
  //           case Environment.Constant(c, _, _) => {
  //             checkArgNumSExpr(printer print funExpr.symbol_,
  //               0, expr.listsexpr_.tail)
  //             c
  //           }
  //           case Environment.Variable(i, BoundVariable(t)) if (t != SMTBool) => {
  //             checkArgNumSExpr(printer print funExpr.symbol_,
  //               0, expr.listsexpr_.tail)
  //             v(i)
  //           }
  //           case _ =>
  //             throw new Parser2InputAbsy.TranslationException(
  //               "Unexpected symbol in a trigger: " +
  //                 (printer print funExpr.symbol_))
  //         }
  //       }
  //     }
  //   }
  // }
  
  // private def translateSExprTail(exprs : ListSExpr) : Seq[ITerm] = {
  //   val args = exprs.tail.toList
  //   for (e <- args) yield translateTrigger(e) match {
  //     case ta : ITerm => ta
  //     case ta : IFormula => ITermITE(ta, i(0), i(1))
  //   }
  // }

  // //////////////////////////////////////////////////////////////////////////////

  // private def translateTreeInterpolantSpec(exprs : ListSExpr)
  //     : List[Tree[Set[Int]]] = {
  //   var result = List[Tree[Set[Int]]]()

  //   for (p <- exprs) p match {
  //     case p : SymbolSExpr =>
  //       result =
  //         List(Tree(Set(partNameIndexes(
  //           env.lookupPartName(printer print p.symbol_))),
  //           result))
  //     case p : ParenSExpr
  //         if (!p.listsexpr_.isEmpty &&
  //           (printer print p.listsexpr_.head) == "and") => {
  //           val it = p.listsexpr_.iterator
  //           it.next
  //           val names = (for (s <- it) yield partNameIndexes(
  //             env.lookupPartName(printer print s))).toSet
  //           result = List(Tree(names, result))
  //         }
  //     case p : ParenSExpr =>
  //       result = result ++ translateTreeInterpolantSpec(p.listsexpr_)
  //   }

  //   result
  // }

  // //////////////////////////////////////////////////////////////////////////////
  

  
  // private def translateChainablePred(args : Seq[Term],
  //   op : (ITerm, ITerm) => IFormula) : IFormula = {
  //   val transArgs = for (a <- args) yield asTerm(translateTerm(a, 0))
  //   connect(for (Seq(a, b) <- transArgs sliding 2) yield op(a, b), IBinJunctor.And)
  // }
  
  // private def flatten(op : String, args : Seq[Term]) : Seq[Term] =
  //   for (a <- args;
  //     b <- collectSubExpressions(a, (t:Term) => t match {
  //       case t : NullaryTerm => t.symbolref_ match {
  //         case PlainSymbol(`op`) => true
  //         case _ => false
  //       }
  //       case t : FunctionTerm => t.symbolref_ match {
  //         case PlainSymbol(`op`) => true
  //         case _ => false
  //       }
  //       case _ => false
  //     }, SMTConnective))
  //   yield b

  // private def checkArgNumLazy(op : => String, expected : Int, args : Seq[Term]) : Unit =
  //   if (expected != args.size) checkArgNum(op, expected, args)
  
  // protected def checkArgNum(op : String, expected : Int, args : Seq[Term]) : Unit =
  //   if (expected != args.size)
  //     throw new Parser2InputAbsy.TranslationException(
  //       "Operator \"" + op +
  //         "\" is applied to a wrong number of arguments: " +
  //         ((for (a <- args) yield (printer print a)) mkString ", "))
  
  // private def checkArgNumSExpr(op : => String, expected : Int, args : Seq[SExpr]) : Unit =
  //   if (expected != args.size)
  //     throw new Parser2InputAbsy.TranslationException(
  //       "Operator \"" + op +
  //         "\" is applied to a wrong number of arguments: " +
  //         ((for (a <- args) yield (printer print a)) mkString ", "))
  
  // private object SMTConnective extends ASTConnective {
  //   def unapplySeq(t : Term) : scala.Option[Seq[Term]] = t match {
  //     case t : NullaryTerm => Some(List())
  //     case t : FunctionTerm => Some(t.listterm_.toList)
  //   }
  // }

  // //////////////////////////////////////////////////////////////////////////////
  


//  protected def asTerm(expr : (MyExpression, SMTType)) : MyTerm = expr match {
//    case (expr : MyTerm, _) =>
//      expr
//    // case (expr : MyFormula, SMTBool) =>
//    //   // ITermITE
//    //   "ITE(" + expr +", 0, 1)"
//    case (expr, _) =>
//      throw new Exception(
//        "Expected a term, not " + expr)
//  }
//
//  private def asTerm(expr : (MyExpression, SMTType),
//    expectedSort : SMTType) : MyTerm = expr match {
//    case (expr : MyTerm, `expectedSort`) =>
//      expr
//    case (expr, _) =>
//      throw new Exception(
//        "Expected a term of type " + expectedSort + ", not " + expr)
//  }
/// EOP
}