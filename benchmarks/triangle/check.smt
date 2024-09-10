(set-logic ALL)

;; Our invariants are:
;  a < ab
;  a < bc
;  a < ac
;  ab > b
;  ab > c
;  bc > b
;  bc > c
;  b < ac
;  ac > c
;  a - ab + b == 0
;  a - ac + c == 0
;  bc - b - c == 0
(define-fun ours ((a Int) (b Int) (c Int) (ab Int) (ac Int) (bc Int)) Bool
    (and 
        (< a ab)
        (< a bc)
        (< b ab)
        (< c ab)
        (< b bc)
        (< c bc)
        (< b ac)
        (< c ac)
        (= (+ a b) ab)
        (= (+ a c) ac)
        (= (+ b c) bc)
    )
) 

;; Evos invariants are:
;  a < ab
;  a < bc
;  a < ac
;  a >= c
;  ab >= bc
;  ab > b
;  ab > c
;  bc > b
;  bc > c
;  b < ac
;  ac > c
;  a - ab + b == 0
;  a - ac + c == 0
;  bc - b - c == 0
(define-fun evos ((a Int) (b Int) (c Int) (ab Int) (ac Int) (bc Int)) Bool
    (and 
        (< a ab)
        (< a bc)
        (< a ac)
        (>= a c)
        (>= ab bc)
        (> ab b)
        (> ab c)
        (> bc b)
        (> bc c)
        (< b ac)
        (< c ac)
        (= (+ a b) ab)
        (= (+ a c) ac)
        (= (+ b c) bc)
    )
) 

(push)
;; Check if ours is a subset of evos.
(assert (forall ((a Int) (b Int) (c Int) (ab Int) (ac Int) (bc Int))
    (=> (ours a b c ab ac bc) (evos a b c ab ac bc))
))
(check-sat)
(pop)

(push)
;; Check if evos is a subset of ours.
(assert (forall ((a Int) (b Int) (c Int) (ab Int) (ac Int) (bc Int))
    (=> (evos a b c ab ac bc) (ours a b c ab ac bc))
))
(check-sat)
(pop)

