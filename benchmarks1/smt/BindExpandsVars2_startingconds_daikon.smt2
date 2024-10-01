
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (n2 Int)  (cp1_off Int)  (n1 Int) ) Bool (and (>= cp1_off 0)(>= n1 0)(>= n2 0)(<= cp1_off n1))) 
(define-fun evo ( (n2 Int)  (cp1_off Int)  (n1 Int) ) Bool (and (>= cp1_off 0)(<= cp1_off n1)))

(push)
(assert (forall ( (n2 Int)  (cp1_off Int)  (n1 Int) ) (=> (ours n2 cp1_off n1) (evo n2 cp1_off n1) )))
(check-sat)
(pop)

(push)
(assert (forall ( (n2 Int)  (cp1_off Int)  (n1 Int) ) (=> (evo n2 cp1_off n1) (ours n2 cp1_off n1) )))
(check-sat)
(pop)
    