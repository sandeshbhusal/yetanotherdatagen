
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (x3 Int)  (x1 Int) ) Bool (= (- (- x1 x3) 150) 0)) 
(define-fun evo ( (x3 Int)  (x1 Int) ) Bool true)

(push)
(assert (forall ( (x3 Int)  (x1 Int) ) (=> (ours x3 x1) (evo x3 x1) )))
(check-sat)
(pop)

(push)
(assert (forall ( (x3 Int)  (x1 Int) ) (=> (evo x3 x1) (ours x3 x1) )))
(check-sat)
(pop)
    