
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (MAXDATA Int)  (mc_i Int)  (cp1_off Int) ) Bool (and (>= mc_i 0)(>= cp1_off 0)(<= cp1_off MAXDATA))) 
(define-fun evo ( (MAXDATA Int)  (mc_i Int)  (cp1_off Int) ) Bool (and (>= mc_i 0)(>= cp1_off 0)(<= cp1_off MAXDATA)))

(push)
(assert (forall ( (MAXDATA Int)  (mc_i Int)  (cp1_off Int) ) (=> (ours MAXDATA mc_i cp1_off) (evo MAXDATA mc_i cp1_off) )))
(check-sat)
(pop)

(push)
(assert (forall ( (MAXDATA Int)  (mc_i Int)  (cp1_off Int) ) (=> (evo MAXDATA mc_i cp1_off) (ours MAXDATA mc_i cp1_off) )))
(check-sat)
(pop)
    