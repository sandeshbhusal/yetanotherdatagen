
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (MAXDATA Int)  (n1 Int)  (cp1_off Int)  (n2 Int) ) Bool (and (<= (- n2) 0)(<= (- cp1_off) 0)(<= (- cp1_off n1) 0)(<= (min2 n1 (- n2 MAXDATA)) 0))) 
(define-fun evo ( (MAXDATA Int)  (n1 Int)  (cp1_off Int)  (n2 Int) ) Bool (and (<= (- cp1_off) 0)(<= (- cp1_off n1) 0)))

(push)
(assert (forall ( (MAXDATA Int)  (n1 Int)  (cp1_off Int)  (n2 Int) ) (=> (ours MAXDATA n1 cp1_off n2) (evo MAXDATA n1 cp1_off n2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (MAXDATA Int)  (n1 Int)  (cp1_off Int)  (n2 Int) ) (=> (evo MAXDATA n1 cp1_off n2) (ours MAXDATA n1 cp1_off n2) )))
(check-sat)
(pop)
    