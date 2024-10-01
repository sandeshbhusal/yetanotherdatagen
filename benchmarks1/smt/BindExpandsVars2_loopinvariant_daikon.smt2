
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (MAXDATA Int)  (cp1_off Int)  (mc_i Int) ) Bool (and (>= mc_i 0)(<= cp1_off MAXDATA))) 
(define-fun evo ( (MAXDATA Int)  (cp1_off Int)  (mc_i Int) ) Bool (and (>= mc_i 0)(>= cp1_off 0)(<= cp1_off MAXDATA)))

(push)
(assert (forall ( (MAXDATA Int)  (cp1_off Int)  (mc_i Int) ) (=> (ours MAXDATA cp1_off mc_i) (evo MAXDATA cp1_off mc_i) )))
(check-sat)
(pop)

(push)
(assert (forall ( (MAXDATA Int)  (cp1_off Int)  (mc_i Int) ) (=> (evo MAXDATA cp1_off mc_i) (ours MAXDATA cp1_off mc_i) )))
(check-sat)
(pop)
    