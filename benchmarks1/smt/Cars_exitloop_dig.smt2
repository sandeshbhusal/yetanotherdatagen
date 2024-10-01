
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (v1 Int)  (v3 Int)  (v2 Int)  (t Int) ) Bool (and (= (- (* t v1) (* t v3)) 0)(= (- (+ (- (pow t 3) (* t (pow v2 2))) (* (* (* 2 t) v2) v3)) (* t (pow v3 2))) 0)(<= (- t) 0)(<= t 11))) 
(define-fun evo ( (v1 Int)  (v3 Int)  (v2 Int)  (t Int) ) Bool (and (= (- (* t v1) (* t v3)) 0)(<= (- t) 0)(<= t 11)))

(push)
(assert (forall ( (v1 Int)  (v3 Int)  (v2 Int)  (t Int) ) (=> (ours v1 v3 v2 t) (evo v1 v3 v2 t) )))
(check-sat)
(pop)

(push)
(assert (forall ( (v1 Int)  (v3 Int)  (v2 Int)  (t Int) ) (=> (evo v1 v3 v2 t) (ours v1 v3 v2 t) )))
(check-sat)
(pop)
    