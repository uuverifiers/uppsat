package uppsat.ast

import scala.collection.mutable.ArrayStack

import uppsat.ModelEvaluator.Model
import uppsat.ast.AST._
import uppsat.precision.PrecisionMap.Path
import uppsat.theory.BitVectorTheory._
import uppsat.theory.BitVectorTheory.BVSortFactory.BVSort
import uppsat.theory.BooleanTheory._
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.theory.IntegerTheory._
import uppsat.theory.IntegerTheory.IntegerSort
import uppsat.theory.RealTheory._

/** Used for packing and unpacking leaf nodes. */
object Leaf {
  val height = 0

  def apply(symbol : ConcreteFunctionSymbol) = new AST(symbol, List(), List())

  def apply(d : ConcreteFunctionSymbol, label : Label ) = AST(d, label, List())

  def unapply(t : AST) : Option[(ConcreteFunctionSymbol, Label)] = t match {
    case AST(d, label, List()) => Some((d, label))
    case _ => None
  }
}

/** Companion object for AST. */
object AST {

  type Label = Path

  def apply(symbol : ConcreteFunctionSymbol,
            children : List[AST] = List()) = new AST(symbol, List(), children)

  // TODO (ptr): Can't this be done by using the one below? By introducing an
  // anonoymous function which just throws away the extra argument.
  /** Perform {@code work} on each node in the tree in a post-order fashion. */
  def postVisit[A](ast : AST, accumulator : A,  work : (A, AST) => A ) : A = {
    val AST(symbol, label, children) = ast
    var accu = accumulator

    for (c <- children)
      accu = postVisit( c, accu, work)

    work(accu, ast)
  }


  /** Perform {@code work} on each node in the tree in a post-order fashion. */
  def postVisit[A,B](ast : AST,
                     accumulator : A,
                     args : B,  work : (B, A, AST) => A ) : A = {
    val AST(symbol, label, children) = ast
    var accu = accumulator

    for (c <- children)
      accu = postVisit( c, accu, args, work)

    work(args, accu, ast)
  }


  /** Perform {@code work} on each node which all ancestors (and itself) is
    * fulfilling {@code cond} in {@code ast} in a pre-order fashion.
    *
    *
    */
  def boolVisit[T](ast : AST,
                   accumulator : T,
                   cond : (T, AST) => Boolean,
                   work : (T, AST) => T ) : T = {
    val AST(symbol, label, children) = ast
    var accu = accumulator

    if (cond(accu, ast)) {
      accu = work(accu, ast)

      for (c <- children)
        accu = boolVisit( c, accu, cond, work)
    }
    accu
  }
}

/** Abstract Syntax Tree.
  *
  */
case class AST(val symbol : ConcreteFunctionSymbol,
               val label : Label,
               val children : List[AST]) {

  case class ASTException(msg : String) extends
      Exception("AST: " + msg)

  lazy val height : Int =
    if (children.isEmpty) 0
    else (children.map(_.height).max + 1)

  lazy val variableCount : Int =
    (if (symbol.theory.isVariable(symbol))
      1
    else
      0) + children.map(_.variableCount).sum

  def getPathOrElse(path : Path) : Option[AST] = {
    val nodes = for (n <- this.iterator.toList if n.label == path) yield n
    nodes.headOption
  }

  def labelAST : AST = {
    // Note: Dual use of path/label
    def labelAux(ast : AST, path: Path) : AST = {
      val AST(symbol, label, children) = ast
      if (label != List())
        throw new Exception("Trying to label an already labeled AST")

      val newChildren =
        for ((c, i) <- children zip children.indices) yield {
          labelAux(c, i :: path)
        }
      AST(symbol, path, newChildren)
    }

    labelAux(this, List(0))
  }

  def iterator = new Iterator[AST] {
    val todo = new ArrayStack[AST]
    todo push (AST.this)
    def hasNext = !todo.isEmpty
    def next = {
      val n = todo.pop()
      todo ++= n.children
      n
    }
  }

  def toList = iterator.toList
  def toSet = iterator.toSet

  def prettyPrint : Unit =
    prettyPrint("")

  def getSMT() = {
      symbol.theory.symbolToSMTLib(symbol)
  }

  def simpleString() : String = {
    children.length match {
      case 0 => getSMT()
      case 1 => getSMT() + " " + children(0).simpleString() + " "
      case 2 => children(0).simpleString() + " " + getSMT() + " " +
          children(1).simpleString()
      case _ => getSMT() + " " + children.map(_.getSMT()).mkString(" ") + " "
    }
  }

  def prettyPrint(indent : String) : Unit = {
    val newIndent = indent + "   "
    println(indent + symbol + " [" + label.mkString(",") + "] //" + symbol.sort)
    for (c <- children) (c prettyPrint newIndent)
  }

  def ppWithModels(indent : String,
                   smallModel : Model,
                   bigModel : Model,
                   diff : Boolean = true) : Unit = {
    val newIndent = indent + "   "
    this.symbol.sort match {
      case BooleanSort if (diff && (smallModel(this) == bigModel(this))) => ()
      case _ => {
        println(indent + symbol + " [" + label.mkString(",") + "] //" +
                  symbol.sort + " " + smallModel(this).symbol + " -> " +
                  bigModel(this).symbol)
          for (c <- children) (c ppWithModels(newIndent, smallModel, bigModel) )
      }
    }
  }

  def size = iterator.size

  def symbols : Set[ConcreteFunctionSymbol]= this.toSet.map(_.symbol)

  def isVariable = symbol.theory.isVariable(symbol)


  //
  //  Syntactic sugar
  //
  def &(that : AST) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (BooleanSort, BooleanSort) => boolAnd(this, that)
       case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 & $s2"
         throw new ASTException(msg)
       }
     }
  }
  
  def unary_! = {
     this.symbol.sort match {
       case BooleanSort => boolNot(this)
       case s => {
         val msg = s"Unsupported syntactic sugar: !$s"
         throw new ASTException(msg)
       }
     }
  }
  
  def unary_- = {
     this.symbol.sort match {
       case IntegerSort => intNegate(this)
       case f : FPSort => floatNegate(this)
       case RealSort => realNegate(this)
       case s => {
         val msg = s"Unsupported syntactic sugar: -$s"
         throw new ASTException(msg)
       }
     }
  }
  
  def +(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (RealSort, RealSort) => realAddition(this, that)
       case (_ : FPSort, _ : FPSort) => floatAddition(this, that)
       case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 + $s2"
         throw new ASTException(msg)
       }
     }
  }
  
  def -(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intSubstraction(this, that)
       case (RealSort, RealSort) => realSubstraction(this, that)
       case (_ : FPSort, _ : FPSort) => floatSubtraction(this, that)
       case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 - $s2"
         throw new ASTException(msg)
       }
  
     }
  }
  
  def *(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (RealSort, RealSort) => realMultiplication(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatMultiplication(this, that)
       case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 * $s2"
         throw new ASTException(msg)
       }
     }
  }
  
  def /(that : AST)(implicit rm : RoundingMode = RoundToZero) = {
     (this.symbol.sort, that.symbol.sort) match {
       //case (IntegerSort, IntegerSort) => intAddition(this, that)
       case (RealSort, RealSort) => realDivision(this, that)
       case (f1 : FPSort, f2 : FPSort) => floatDivision(this, that)
       case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 / $s2"
         throw new ASTException(msg)
       }
     }
  }
  
  //TODO: Check which one to use
  def ===(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (BooleanSort, BooleanSort) => boolEquality(this, that)
      case (IntegerSort, IntegerSort) => intEquality(this, that)
      case (RealSort, RealSort) => realEquality(this, that)
      case (f1 : FPSort, f2 : FPSort) => floatEquality(this, that)
      case (RoundingModeSort, RoundingModeSort) => rmEquality(this, that)
      case (bv1 : BVSort, bv2 : BVSort) => bvEquality(this, that)
      case (s1, s2) => {
         val msg = s"Unsupported syntactic sugar: $s1 === $s2"
         throw new ASTException(msg)
       }
     }
  }
  
  def <=(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (IntegerSort, IntegerSort) => intLessThanOrEqual(this, that)
      case (RealSort, RealSort) => realLessThanOrEqual(this, that)
      case (f1 : FPSort, f2 : FPSort) => floatLessThanOrEqual(this, that)
      case (s1, s2) => {
        val msg = s"Unsupported syntactic sugar: $s1 <= $s2"
        throw new ASTException(msg)
      }
    }
  }
  
  def <(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (RealSort, RealSort) => realLessThan(this, that)
      case (f1 : FPSort, f2 : FPSort) => floatLessThan(this, that)
      case (s1, s2) => {
        val msg = s"Unsupported syntactic sugar: $s1 < $s2"
        throw new ASTException(msg)
      }
    }
  }
  
  def >=(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (RealSort, RealSort) => realGreaterThanOrEqual(this, that)
      case (_ : FPSort, _ : FPSort) => floatGreaterThanOrEqual(this, that)
      case (s1, s2) => {
        val msg = s"Unsupported syntactic sugar: $s1 >= $s2"
        throw new ASTException(msg)
      }
    }
  }
  
  def >(that : AST) = {
    (this.symbol.sort, that.symbol.sort) match {
      case (RealSort, RealSort) => realGreaterThan(this, that)
      case (f1 : FPSort, f2 : FPSort) => floatGreaterThan(this, that)
      case (s1, s2) => {
        val msg = s"Unsupported syntactic sugar: $s1 > $s2"
        throw new ASTException(msg)
      }
    }
  }
}

// TODO: How do we handle quantifiers. Should we have different types of AST?
// TODO: Sharing, how do we accommodate? Enforcing it (seems like a bad idea?)
// TODO: We can use implicit conversion
