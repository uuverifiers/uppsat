(set-logic QF_FP)

(declare-fun .10 () (_ FloatingPoint 11 53))
(declare-fun .11 () (_ FloatingPoint 11 53))
(declare-fun .12 () (_ FloatingPoint 11 53))
(declare-fun .13 () Bool)
(declare-fun .14 () (_ FloatingPoint 11 53))
(declare-fun .15 () (_ FloatingPoint 11 53))
(declare-fun .16 () Bool)
(declare-fun .17 () Bool)
(declare-fun .3 () RoundingMode)
(declare-fun equal0 () Bool)
(declare-fun equal1 () Bool)
(declare-fun equal13 () Bool)
(declare-fun equal3 () Bool)
(declare-fun equal6 () Bool)
(declare-fun equal7 () Bool)
(declare-fun equal9 () Bool)
(declare-fun equality11 () Bool)
(declare-fun equality2 () Bool)
(declare-fun equality4 () Bool)
(declare-fun fp-to-fp5 () (_ FloatingPoint 11 53))
(declare-fun less-than10 () Bool)
(declare-fun multiplication8 () (_ FloatingPoint 11 53))
(declare-fun nary-conjunction14 () Bool)
(declare-fun rounding-mode-equality12 () Bool)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(declare-fun z () (_ FloatingPoint 11 53))

(assert (= equal0 (= .14 x)))
(assert (= equal1 (= .11 .12)))
(assert (= equal13 (= .11 z)))
(assert (= equal3 (= .14 .15)))
(assert (= equal6 (= .10 ((_ to_fp 11 53) RTZ (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))))
(assert (= equal7 (= .12 y)))
(assert (= equal9 (= .15 (fp.mul .3 .11 .12))))
(assert (= equality11 (= .17 (fp.lt .14 .10))))
(assert (= equality2 (= .13 (= .11 .12))))
(assert (= equality4 (= .16 (= .14 .15))))
(assert (= fp-to-fp5 ((_ to_fp 11 53) RTZ (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000))))
(assert (= less-than10 (fp.lt .14 .10)))
(assert (= multiplication8 (fp.mul .3 .11 .12)))
(assert (= nary-conjunction14 (and .13 (= .14 x) (= .13 (= .11 .12)) (= .16 (= .14 .15)) (= .10 ((_ to_fp 11 53) RTZ (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000))) (= .12 y) (= .15 (fp.mul .3 .11 .12)) (= .17 (fp.lt .14 .10)) (= .3 RNE) (= .11 z))))
(assert (= rounding-mode-equality12 (= .3 RNE)))
(assert (and .13 (= .14 x) (= .13 (= .11 .12)) (= .16 (= .14 .15)) (= .10 ((_ to_fp 11 53) RTZ (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000))) (= .12 y) (= .15 (fp.mul .3 .11 .12)) (= .17 (fp.lt .14 .10)) (= .3 RNE) (= .11 z)))

(check-sat)












































