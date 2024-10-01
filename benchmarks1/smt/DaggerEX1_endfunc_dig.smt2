
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours () Bool true) 
(define-fun evo () Bool true)

(push)
(assert (forall () (=> (ours ) (evo ) )))
(check-sat)
(pop)

(push)
(assert (forall () (=> (evo ) (ours ) )))
(check-sat)
(pop)
    