(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun q () Int)
(declare-fun r () Int)

(define-fun subset () Set
(union (>= a -10) (<= a -5)))

; Does not work.
;(assert (= (implies parent subset) true))
;(assert (= (not (implies subset parent)) true))

; Does not work.
;(assert (= parent true))
;(assert (= subset true))
;(assert (= (implies parent subset) true))

; Does not work.
;(assert (not (= b a )))
;(assert (= parent true))
;(assert (= subset true))
;(assert (= (implies parent subset) true))

(check-sat)
(get-model)

