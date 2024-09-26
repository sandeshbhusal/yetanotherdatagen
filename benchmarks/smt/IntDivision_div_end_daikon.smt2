
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (r Int)  (q Int)  (a Int)  (b Int) ) Bool (and (>= q 1)(>= b 1)(>= r 0)(>= a q)(>= a b)(> a r)(> b r))) 
(define-fun evo ( (r Int)  (q Int)  (a Int)  (b Int) ) Bool (and (>= q 1)(>= r 0)(>= a b)(> a r)(> b r)))

(push)
(assert (forall ( (r Int)  (q Int)  (a Int)  (b Int) ) (=> (ours r q a b) (evo r q a b) )))
(check-sat)
(pop)

(push)
(assert (forall ( (r Int)  (q Int)  (a Int)  (b Int) ) (=> (evo r q a b) (ours r q a b) )))
(check-sat)
(pop)
    