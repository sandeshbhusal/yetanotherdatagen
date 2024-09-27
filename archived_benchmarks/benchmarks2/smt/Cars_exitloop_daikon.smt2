
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (t Int) ) Bool (>= t 0)) 
(define-fun evo ( (t Int) ) Bool (>= t 0))

(push)
(assert (forall ( (t Int) ) (=> (ours t) (evo t) )))
(check-sat)
(pop)

(push)
(assert (forall ( (t Int) ) (=> (evo t) (ours t) )))
(check-sat)
(pop)
    