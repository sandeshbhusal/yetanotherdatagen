
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (x3 Int)  (x1 Int)  (x2 Int) ) Bool (and (= (- (- x1 x3) 150) 0)(<= (+ (- x1) x2) (- 15)))) 
(define-fun evo ( (x3 Int)  (x1 Int)  (x2 Int) ) Bool (= (+ (+ (- x1) x3) 150) 0))

(push)
(assert (forall ( (x3 Int)  (x1 Int)  (x2 Int) ) (=> (ours x3 x1 x2) (evo x3 x1 x2) )))
(check-sat)
(pop)

(push)
(assert (forall ( (x3 Int)  (x1 Int)  (x2 Int) ) (=> (evo x3 x1 x2) (ours x3 x1 x2) )))
(check-sat)
(pop)
    