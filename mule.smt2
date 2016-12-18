(set-info :status unknown)
(set-info :source |Alberto Griggio <griggio@fbk.eu>. These benchmarks were used for the evaluation in the following paper: L. Haller, A. Griggio, M. Brain, D. Kroening: Deciding floating-point logic with systematic abstraction. FMCAD 2012.)|)
(set-logic QF_FPBV)
(declare-fun b25 () (_ FloatingPoint 8 24))
(declare-fun b14 () (_ FloatingPoint 11 53))
(declare-fun b28 () (_ FloatingPoint 8 24))
(declare-fun b20 () (_ FloatingPoint 11 53))
(declare-fun b9 () (_ FloatingPoint 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FloatingPoint 8 24) b9)
(define-fun .10 () (_ FloatingPoint 8 24) (fp.mul .3 .9 .9))
(define-fun .11 () (_ FloatingPoint 8 24) (fp.add .3 .9 .10))
(define-fun .12 () (_ FloatingPoint 11 53) ((_ to_fp 11 53) .3 .11))
(define-fun .13 () (_ FloatingPoint 11 53) b20)
(define-fun .14 () Bool (fp.lt .12 .13))
(define-fun .15 () Bool (not .14))
(define-fun .16 () (_ FloatingPoint 8 24) b28)
(define-fun .17 () Bool (fp.leq .16 .9))
(define-fun .18 () (_ FloatingPoint 8 24) b25)
(define-fun .19 () Bool (fp.leq .9 .18))
(define-fun .20 () Bool (and .17 .19))
(define-fun .21 () Bool (and .15 .20))
(define-fun .22 () (_ FloatingPoint 11 53) b14)
(define-fun .23 () Bool (fp.lt .12 .22))
(define-fun .24 () Bool (and .21 .23))
(assert .24)
(check-sat)
(get-model)