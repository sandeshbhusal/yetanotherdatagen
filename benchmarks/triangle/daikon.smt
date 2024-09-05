(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const ab Int)
(declare-const bc Int)
(declare-const ac Int)

; Set 1: Invariants
(define-fun set1 () Bool
(and (>= a 1) (< a ab) (< a bc) (< a ac) (> ab b) (> ab c) (> bc b) (> bc c) (< b ac) (> ac c)
(= (- (- a ab) b) 0) (= (- (- a ac) c) 0) (= (- (- bc b) c) 0)))
; Set 2: Invariants
(define-fun set2 () Bool
(and (< a ab) (< a bc) (< a ac) (<= a c) (<= ab bc) (> ab b) (> ab c) (> bc b) (> bc c) (< b ac) (> ac c)
(= (- (- a ab) b) 0) (= (- (- a ac) c) 0) (= (- (- bc b) c) 0)))


(push)
; Check if Set 1 is a subset of Set 2
(assert (and set1 (not set2)))
(check-sat)
(get-model)
(pop)

(push)
; Check if Set 2 is a subset of Set 1
(assert (and set2 (not set1)))
(check-sat)
(get-model)
(pop)
