package uppsat;

import uppsat.approximation.Approximation
import uppsat.approximation.smallints.SmallIntsApp
import uppsat.approximation.fpa.fixpoint.
   {FPABVApp,FPABVNodeByNodeApp, FPABVEmptyApp}
import uppsat.approximation.fpa.reals.
  {FPARealApp, FPARealNodeByNodeApp, FxPntFPARealApp}
import uppsat.approximation.fpa.smallfloats.
  {IJCARSmallFloatsApp, FxPntSmallFloatsApp, IJCARSmallFloatsNodeByNodeApp, IJCARSmallFloatsEmptyapp}
import uppsat.approximation.empty.EmptyApp


object RegisteredApproximations {
  val regApproxs = Map(
    ("empty" ->
       ("Empty approximation",
        () => new Approximation(EmptyApp))),

    ("ijcar" ->
       ("The SmallFloats approximation introduced at IJCAR 2014",
        () => new Approximation(IJCARSmallFloatsApp))),

    ("saturation" ->
       ("Saturation based approximation",
        () => new Approximation(FxPntSmallFloatsApp))),

    ("ijcar-node-by-node" ->
       ("SmallFloats using node-by-node",
        () => new Approximation(IJCARSmallFloatsNodeByNodeApp))),

    ("ijcar-no-reconstruct" ->
       ("SmallFloats with no reconstruction",
        () => new Approximation(IJCARSmallFloatsEmptyapp))),

    ("smallints" ->
       ("SmallInts approximation",
        () => new Approximation(SmallIntsApp))),

    ("reals" ->
       ("Real approximation of floating points",
        () => new Approximation(FPARealApp))),

    ("reals-node-by-node" ->
       ("Real approximation using node-by-node",
        () => new Approximation(FPARealNodeByNodeApp))),

    ("saturation_reals" ->
       ("Real approximation using saturation",
        () => new Approximation(FxPntFPARealApp))),

    ("fixedpoint" ->
       ("Fixed-point approximation of floating points",
        () => new Approximation(FPABVApp))),

    ("fixedpoint-node-by-node" ->
       ("Fixed-point using node-by-node",
        () => new Approximation(FPABVNodeByNodeApp))),

    ("fixedpoint-no-reconstruct" ->
       (("Fixed-point with no reconstruction",
         () => new Approximation(FPABVEmptyApp))))
  )
}
