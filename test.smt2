(set-logic QF_FPABV)
(declare-fun x () (_ FP 11 53))
(declare-fun y () (_ FP 11 53))

(assert (= x y))

(check-sat)