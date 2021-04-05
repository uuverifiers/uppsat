(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :category "crafted")
(set-info :source "Regression test benchmark for UppSAT.")
(set-info :status sat)


(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
(assert (= a b))

(check-sat)
