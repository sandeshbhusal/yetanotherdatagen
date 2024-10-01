
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (x1 Int)  (x3 Int)  (x2 Int) ) Bool (and (> x1 x2)(= (- (- x1 x3) 150) 0)(> x2 x3))) 
(define-fun evo ( (x1 Int)  (x3 Int)  (x2 Int) ) Bool (and (> x1 x2)(= (- (- x1 x3) 150) 0)(> x2 x3)))

(push)
(assert (forall ( (x1 Int)  (x3 Int)  (x2 Int) ) (=> (ours x1 x3 x2) (evo x1 x3 x2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (x1 Int)  (x3 Int)  (x2 Int) ) (=> (evo x1 x3 x2) (ours x1 x3 x2) )))
(check-sat)
(pop)
    