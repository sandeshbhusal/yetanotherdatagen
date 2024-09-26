
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (mc_i Int)  (MAXDATA Int)  (cp1_off Int) ) Bool (and (>= mc_i 0)(< mc_i MAXDATA))) 
(define-fun evo ( (mc_i Int)  (MAXDATA Int)  (cp1_off Int) ) Bool (and (>= mc_i 0)(>= cp1_off 0)(< mc_i MAXDATA)))

(push)
(assert (forall ( (mc_i Int)  (MAXDATA Int)  (cp1_off Int) ) (=> (ours mc_i MAXDATA cp1_off) (evo mc_i MAXDATA cp1_off) )))
(check-sat)
(pop)

(push)
(assert (forall ( (mc_i Int)  (MAXDATA Int)  (cp1_off Int) ) (=> (evo mc_i MAXDATA cp1_off) (ours mc_i MAXDATA cp1_off) )))
(check-sat)
(pop)
    