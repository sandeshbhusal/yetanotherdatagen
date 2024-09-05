(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun ac () Int)
(declare-fun bc () Int)
(declare-fun ab () Int)

(define-fun min ((x Int) (y Int)) Int
  (ite (<= x y) x y)
)

(define-fun ours () Bool
  (and
    (= (- b bc c) 0)
    (= (- a ac c) 0)
    (= (- ab ac bc (* 2 c)) 0)
    (<= (- a bc) -1)
    (<= (- ac b) -1)
    (<= (- ab c) -1)
  )
)

(define-fun current () Bool
   (and
    (= (- a ac c) 0)                     ; a - ac + c == 0
    (= (- b bc c) 0)                     ; b - bc + c == 0
    (= (- ab ac bc (* 2 c)) 0)           ; ab - ac - bc + 2*c == 0
    (<= (- a c) 0)                        ; a - c <= 0
    (<= (- ab bc) 0)                      ; ab - bc <= 0
    (<= (- ac b) -1)                      ; -ac + b <= -1
    (<= (- ab c) -1)                      ; -ab + c <= -1
    (<= (min ac bc) ab)                  ; min(ac, bc) - ab <= 0
  )     
)

; Check if (implies inv1 inv2) is valid
(push)
(assert (and ours (not current)))
(check-sat)
(get-model)
(pop)

; Check if (implies inv2 inv1) is valid
(push)
(assert (and current (not ours)))
(check-sat)
(get-model)
(pop)
