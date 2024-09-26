
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (t Int)  (v3 Int)  (v1 Int) ) Bool (and (= (- (* t v1) (* t v3)) 0)(<= (- t) 0))) 
(define-fun evo ( (t Int)  (v3 Int)  (v1 Int) ) Bool (and (= (- (* t v1) (* t v3)) 0)(<= (- t) 0)(<= t 11)))

(push)
(assert (forall ( (t Int)  (v3 Int)  (v1 Int) ) (=> (ours t v3 v1) (evo t v3 v1) )))
(check-sat)
(pop)

(push)
(assert (forall ( (t Int)  (v3 Int)  (v1 Int) ) (=> (evo t v3 v1) (ours t v3 v1) )))
(check-sat)
(pop)
    