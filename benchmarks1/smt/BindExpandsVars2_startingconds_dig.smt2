
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (MAXDATA Int)  (n2 Int)  (cp1_off Int)  (n1 Int) ) Bool (and (<= (- n2) 0)(<= (- cp1_off) 0)(<= (- cp1_off n1) 0)(<= (min2 n1 (- n2 MAXDATA)) 0))) 
(define-fun evo ( (MAXDATA Int)  (n2 Int)  (cp1_off Int)  (n1 Int) ) Bool (and (<= (- n2) 0)(<= (- cp1_off) 0)(<= (- cp1_off n1) 0)))

(push)
(assert (forall ( (MAXDATA Int)  (n2 Int)  (cp1_off Int)  (n1 Int) ) (=> (ours MAXDATA n2 cp1_off n1) (evo MAXDATA n2 cp1_off n1) )))
(check-sat)
(pop)

(push)
(assert (forall ( (MAXDATA Int)  (n2 Int)  (cp1_off Int)  (n1 Int) ) (=> (evo MAXDATA n2 cp1_off n1) (ours MAXDATA n2 cp1_off n1) )))
(check-sat)
(pop)
    