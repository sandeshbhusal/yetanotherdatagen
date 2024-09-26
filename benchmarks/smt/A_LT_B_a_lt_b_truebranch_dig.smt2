
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (a Int)  (b Int) ) Bool (<= (- a b) (- 1))) 
(define-fun evo ( (a Int)  (b Int) ) Bool (<= (- a b) (- 1)))

(push)
(assert (forall ( (a Int)  (b Int) ) (=> (ours a b) (evo a b) )))
(check-sat)
(pop)

(push)
(assert (forall ( (a Int)  (b Int) ) (=> (evo a b) (ours a b) )))
(check-sat)
(pop)
    