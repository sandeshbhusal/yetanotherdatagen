
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (n1 Int)  (cp1_off Int)  (n2 Int) ) Bool (and (>= cp1_off 0)(>= n1 0)(>= n2 0)(<= cp1_off n1))) 
(define-fun evo ( (n1 Int)  (cp1_off Int)  (n2 Int) ) Bool (and (>= cp1_off 0)(>= n1 0)(>= n2 0)(<= cp1_off n1)))

(push)
(assert (forall ( (n1 Int)  (cp1_off Int)  (n2 Int) ) (=> (ours n1 cp1_off n2) (evo n1 cp1_off n2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (n1 Int)  (cp1_off Int)  (n2 Int) ) (=> (evo n1 cp1_off n2) (ours n1 cp1_off n2) )))
(check-sat)
(pop)
    