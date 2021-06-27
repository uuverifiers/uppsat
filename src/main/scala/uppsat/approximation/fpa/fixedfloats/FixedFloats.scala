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
    BVSubFactory => BVSUB,
    BVSortFactory, BVVar}
import uppsat.theory.BooleanTheory.boolNaryAnd
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

  override def encodeFormula(ast : AST,
                             pmap : PrecisionMap[Precision]) : AST = {
    // TODO (FF): We assume 32-bits or 64-bits standard FP numbers for now
    // TODO (FF): Come up with better names for auxilliary variables

    val maxDistance =
      if (globalOptions.FF_SPED)
        globalOptions.INFO_MAP("SPED").toInt
      else
        pmap.max.asInstanceOf[Int]

    val constraints = arithmeticBounds(ast, maxDistance)

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
