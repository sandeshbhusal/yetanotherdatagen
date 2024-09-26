
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (MAXDATA Int)  (cp1_off Int)  (n1 Int)  (n2 Int) ) Bool (and (>= cp1_off 0)(>= n2 0)(<= cp1_off n1)(<= n2 MAXDATA))) 
(define-fun evo ( (MAXDATA Int)  (cp1_off Int)  (n1 Int)  (n2 Int) ) Bool (and (>= cp1_off 0)(>= n1 0)(>= n2 0)(<= cp1_off n1)(<= n2 MAXDATA)))

(push)
(assert (forall ( (MAXDATA Int)  (cp1_off Int)  (n1 Int)  (n2 Int) ) (=> (ours MAXDATA cp1_off n1 n2) (evo MAXDATA cp1_off n1 n2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (MAXDATA Int)  (cp1_off Int)  (n1 Int)  (n2 Int) ) (=> (evo MAXDATA cp1_off n1 n2) (ours MAXDATA cp1_off n1 n2) )))
(check-sat)
(pop)
    