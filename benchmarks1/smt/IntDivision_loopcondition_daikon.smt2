
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (a Int)  (b Int)  (r Int)  (q Int) ) Bool (and (>= q 0)(>= a b)(<= b r))) 
(define-fun evo ( (a Int)  (b Int)  (r Int)  (q Int) ) Bool (and (>= q 0)(>= a b)(<= b r)))

(push)
(assert (forall ( (a Int)  (b Int)  (r Int)  (q Int) ) (=> (ours a b r q) (evo a b r q) )))
(check-sat)
(pop)

(push)
(assert (forall ( (a Int)  (b Int)  (r Int)  (q Int) ) (=> (evo a b r q) (ours a b r q) )))
(check-sat)
(pop)
    