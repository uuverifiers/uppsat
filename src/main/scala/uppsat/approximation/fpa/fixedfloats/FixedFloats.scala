package uppsat.approximation.fpa.fixedfloats

/*
 * FixedFloats version 1.0
 *
 * Lets try to only do exponential range limiting. I.e., we put a variable "EXP"
 * which is "middle"-value for all exponent values. Then make sure all exponents
 * lies within "DIST" distance of this value.
 *
 */

import uppsat.globalOptions
import uppsat.globalOptions.verbose
import uppsat.ModelEvaluator.Model
import uppsat.approximation.Codec
import uppsat.approximation.ApproximationContext
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.refinement.
  {UniformPGRefinementStrategy, UniformMGRefinementStrategy}
import uppsat.approximation.toolbox.Toolbox
import uppsat.ast.{AST, ConcreteFunctionSymbol, Leaf}
import uppsat.ast.AST.Label
import uppsat.precision.{IntPrecisionOrdering, PrecisionMap}
import uppsat.theory.{BitVectorTheory, FloatingPointTheory}
import uppsat.theory.BitVectorTheory.
  {bv,
    BVEqualityFactory => BVEQ,
    BVLessThanOrEqualFactory => BVSLE,
    BVAddFactory => BVADD,
    BVSubFactory => BVSUB,
    BVSortFactory, BVVar}
import uppsat.theory.BooleanTheory.{boolNaryAnd, boolNaryOr}
import uppsat.theory.FloatingPointTheory.
  {BVTripleToFPFactory => BVT, FPEqualityFactory => FPEQ, isFPVariable}
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort

/** Empty theory for using backend solver */
trait FixedFloatsContext extends ApproximationContext {
  type Precision = Int

  // TODO (FF): What is a good upper bound?
  val precisionOrdering = new IntPrecisionOrdering(0,32)
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
}

trait FixedFloatsCodec extends Codec {

  // Useful constants
  val SIGN_SORT = BVSortFactory(List(1))

  val EXP_SORT32 = BVSortFactory(List(8))
  val EXP_SORT64 = BVSortFactory(List(11))

  val SIG_SORT32 = BVSortFactory(List(23))
  val SIG_SORT64 = BVSortFactory(List(52))

  val BV_ONE32 = Leaf(bv(List(0,0,0,0,0,0,0,1))(BVSortFactory.BVSort(8)))
  val BV_ONE64 = Leaf(bv(List(0,0,0,0,0,0,0,0,0,0,1))(BVSortFactory.BVSort(11)))

  def decodeNode(args: (Model, PrecisionMap[Precision]),
                 decodedModel : Model,
                 ast : AST) = {
    val (appModel, _) = args
    decodedModel.checkSet(ast, appModel(ast))
    decodedModel
  }


  def decodeModel(ast : AST,
                  appModel : Model,
                  pmap : PrecisionMap[Precision]) : Model = {
    val decodedModel = new Model()
    AST.postVisit(ast, decodedModel, (appModel, pmap), decodeNode)
    decodedModel
  }

  /**
    * We need to override since we need a global symbol for exponent
    */


  def arithmeticBounds(ast : AST, maxDistance : Int) : AST = {
   val bits = maxDistance.toBinaryString

    val LIMIT_VALUE32 =
      (("0"*(8 - bits.length)) + bits).toList.map(_.toInt - 48)
    val LIMIT_VALUE64 =
      (("0"*(11 - bits.length)) + bits).toList.map(_.toInt - 48)

    val MIDDLE32 = BVVar("__EXP_MIDDLE32__", EXP_SORT32)
    val MIDDLE64 = BVVar("__EXP_MIDDLE64__", EXP_SORT64)

    val MIDDLE_VALUE32 = List(0,0,0,0,0,0,0,0)
    val MIDDLE_VALUE64 = List(0,0,0,0,0,0,0,0,0,0,0)

    val LIMIT32 = BVVar("__LIMIT32__", EXP_SORT32)
    val LIMIT64 = BVVar("__LIMIT64__", EXP_SORT64)




    // Add a variable corresponding to each floating point exponent bits
    val fpVariables = ast.variables().filter(isFPVariable)

    // Each tuple is (FP Var, isDouble, Sign Var, Exponent Var, Mantissa Var)
    val varPairs = for (v <- fpVariables) yield {
      val sign = BVVar(Toolbox.suffixVariable(v.name, "sign"), SIGN_SORT)
      val (exponent, significant, double) =
        v.sort match {
          case FPSort(8, 24) =>
            (BVVar(Toolbox.suffixVariable(v.name, "exp"), EXP_SORT32),
             BVVar(Toolbox.suffixVariable(v.name, "mant"), SIG_SORT32),
             false)

          case FPSort(11, 53) =>
            (BVVar(Toolbox.suffixVariable(v.name, "exp"), EXP_SORT64),
             BVVar(Toolbox.suffixVariable(v.name, "mant"), SIG_SORT64),
             true)
          case FPSort(eb, sb) => throw new Exception(s"FPSort: $eb $sb")
          case s => throw new Exception(s"unhandled sort: $s")
        }
      (v, sign, exponent, significant, double)
    }


    // Ensure distance to MIDDLE
    val mvConstraints = (for ((fp, _, eb, _, double) <- varPairs) yield {
                           val bvEquality =
                             if (double)
                               BVEQ(EXP_SORT32)
                             else
                               BVEQ(EXP_SORT64)

                           val middleValue =
                             if (double)
                               Leaf(MIDDLE64)
                             else
                               Leaf(MIDDLE32)

                           val limit =
                             if (double)
                               Leaf(LIMIT64)
                             else
                               Leaf(LIMIT32)

                           val bvsle = BVSLE(eb.sort)
                           val bvsub = BVSUB(eb.sort)
                           val case1 = AST(bvsub, List(Leaf(eb), middleValue))
                           val case2 = AST(bvsub, List(middleValue, Leaf(eb)))
                           val case11 = AST(bvsle, List(case1, limit))
                           val case22 = AST(bvsle, List(case2, limit))

                           List(case11, case22)
                         }).flatten

    // Ensure equality with exponential bits
    val ebConstraints = for ((fp, sign, eb, mb, double) <- varPairs) yield {
      val symbol = BVT(fp.sort)
      val fpNode = AST(symbol, List(Leaf(sign), Leaf(eb), Leaf(mb)))
      val eqSymbol = FPEQ(fp.sort)
      AST(eqSymbol, List(Leaf(fp), fpNode))
    }

    // Constraint LIMIT to some value (Precision?)
    val limitConstant32 =
      bv(LIMIT_VALUE32)(LIMIT32.sort)
    val limitConstraint32 =
      AST(BVEQ(LIMIT32.sort), List(Leaf(LIMIT32), Leaf(limitConstant32)))

    val limitConstant64 =
      bv(LIMIT_VALUE64)(LIMIT64.sort)
    val limitConstraint64 =
      AST(BVEQ(LIMIT64.sort), List(Leaf(LIMIT64), Leaf(limitConstant64)))

    // Constrain MIDDLE to some value
    val middleConstant32 =
      bv(MIDDLE_VALUE32)(MIDDLE32.sort)
    val middleConstraint32 =
      AST(BVEQ(MIDDLE32.sort), List(Leaf(MIDDLE32), Leaf(middleConstant32)))

    val middleConstant64 =
      bv(MIDDLE_VALUE64)(MIDDLE64.sort)
    val middleConstraint64 =
      AST(BVEQ(MIDDLE64.sort), List(Leaf(MIDDLE64), Leaf(middleConstant64)))


    if (globalOptions.FF_MIDDLE_ZERO)
      boolNaryAnd(middleConstraint32 :: middleConstraint64 ::
                    limitConstraint32 :: limitConstraint64 ::
                    (mvConstraints.toList ++ ebConstraints))
    else
      boolNaryAnd(limitConstraint32 :: limitConstraint64 ::
                    (mvConstraints.toList ++ ebConstraints))
  }


  def choiceBounds(ast : AST, maxDistance : Int) : AST = {
    // Given maxDistance of x, we have 2*x+1 possible values, so we create 2x+1
    // fp-constants, ensuring that each is one greater than the previous, and
    // create a disjunction equalizing each exponent with one of them.

    // We need to do this process once for 32-bits and once for 64-bits

    val EXP_SORT32 = BVSortFactory(List(8))
    // val EXP_SORT64 = BVSortFactory(List(11))



    // Add a variable corresponding to each floating point exponent bits
    val fpVariables = ast.variables().filter(isFPVariable)

    // Each tuple is (FP Var, isDouble, Sign Var, Exponent Var, Mantissa Var)
    val varPairs = for (v <- fpVariables) yield {
      val sign = BVVar(Toolbox.suffixVariable(v.name, "sign"), SIGN_SORT)
      val (exponent, significant, double) =
        v.sort match {
          case FPSort(8, 24) =>
            (BVVar(Toolbox.suffixVariable(v.name, "exp"), EXP_SORT32),
             BVVar(Toolbox.suffixVariable(v.name, "mant"), SIG_SORT32),
             false)

          case FPSort(11, 53) =>
            (BVVar(Toolbox.suffixVariable(v.name, "exp"), EXP_SORT64),
             BVVar(Toolbox.suffixVariable(v.name, "mant"), SIG_SORT64),
             true)
          case FPSort(eb, sb) => throw new Exception(s"FPSort: $eb $sb")
          case s => throw new Exception(s"unhandled sort: $s")
        }
      (v, sign, exponent, significant, double)
    }


    // Ensure equality with exponential bits
    val ebConstraints = for ((fp, sign, eb, mb, double) <- varPairs) yield {
      val symbol = BVT(fp.sort)
      val fpNode = AST(symbol, List(Leaf(sign), Leaf(eb), Leaf(mb)))
      val eqSymbol = FPEQ(fp.sort)
      AST(eqSymbol, List(Leaf(fp), fpNode))
    }

    // 32-bits
    val choices32 =
      (for (i <- 0 to (2*maxDistance)) yield {
        BVVar(s"__EXP_CHOICE32_${i}__", EXP_SORT32)
      }).toList

    val addConstraints32 =
      (for (i <- 0 until (2*maxDistance)) yield {
        val bvadd = BVADD(EXP_SORT32)
        val addNode = AST(bvadd, List(Leaf(choices32(i)), BV_ONE32))
        addNode === Leaf(choices32(i+1))
      }).toList

    // Ensure equality with exponential bits
    val eqConstraints32 =
      (for ((_, _, eb, _, double) <- varPairs; if !double) yield {
        boolNaryOr(for (c <- choices32) yield Leaf(eb) === Leaf(c))
      }).toList


    // 64-bits
    val choices64 =
      (for (i <- 0 to (2*maxDistance)) yield {
         BVVar(s"__EXP_CHOICE64_${i}__", EXP_SORT64)
       }).toList

    val addConstraints64 =
      (for (i <- 0 until (2*maxDistance)) yield {
         val bvadd = BVADD(EXP_SORT64)
         val addNode = AST(bvadd, List(Leaf(choices64(i)), BV_ONE64))
         addNode === Leaf(choices64(i+1))
       }).toList

    // Ensure equality with exponential bits
    val eqConstraints64 =
      (for ((_, _, eb, _, double) <- varPairs; if double) yield {
         boolNaryOr(for (c <- choices64) yield Leaf(eb) === Leaf(c))
       }).toList

    boolNaryAnd(addConstraints32 ++ eqConstraints32 ++ addConstraints64 ++ eqConstraints64)
  }


  override def encodeFormula(ast : AST,
                             pmap : PrecisionMap[Precision]) : AST = {
    // TODO (FF): We assume 32-bits or 64-bits standard FP numbers for now
    // TODO (FF): Come up with better names for auxilliary variables

    val maxDistance =
      if (globalOptions.FF_SPED)
        globalOptions.INFO_MAP("SPED").toInt
      else
        pmap.max.asInstanceOf[Int]

    val constraints =
      if (globalOptions.FF_BOUNDS) {
        globalOptions.verbose("Using choice bounds")
        choiceBounds(ast,maxDistance)
      } else {
        globalOptions.verbose("Using arithmetic bounds")
        arithmeticBounds(ast, maxDistance)
      }

    val newAst = ast & constraints

    if (globalOptions.FORMULAS) {
      println("<<Starting formula>>")
      ast.prettyPrint
      println("<<New formula>>")
      newAst.prettyPrint
    }

    newAst
  }



}

trait FixedFloatsPGRefinementStrategy extends UniformPGRefinementStrategy {
  def unsatRefinePrecision( p : Int) : Int = {
    p + 1
  }
}

trait FixedFloatsMGRefinementStrategy extends UniformMGRefinementStrategy {
  def satRefinePrecision( p : Int) : Int = {
    p + 1
  }

}

object FixedFloatsApp extends FixedFloatsContext
    with FixedFloatsCodec
    with EmptyReconstruction
    with FixedFloatsPGRefinementStrategy
    with FixedFloatsMGRefinementStrategy
