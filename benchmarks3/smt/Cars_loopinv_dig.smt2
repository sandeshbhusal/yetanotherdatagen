
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (v2 Int) ) Bool (and (<= v2 5)(<= (- v2) 5))) 
(define-fun evo ( (v2 Int) ) Bool (and (<= v2 5)(<= (- v2) 5)))

(push)
(assert (forall ( (v2 Int) ) (=> (ours v2) (evo v2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (v2 Int) ) (=> (evo v2) (ours v2) )))
(check-sat)
(pop)
    