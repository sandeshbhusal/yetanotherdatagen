
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (b Int)  (a Int) ) Bool (>= a b)) 
(define-fun evo ( (b Int)  (a Int) ) Bool true)

(push)
(assert (forall ( (b Int)  (a Int) ) (=> (ours b a) (evo b a) )))
(check-sat)
(pop)

(push)
(assert (forall ( (b Int)  (a Int) ) (=> (evo b a) (ours b a) )))
(check-sat)
(pop)
    