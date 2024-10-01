
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (c Int)  (a Int)  (b Int)  (ac Int)  (ab Int)  (bc Int) ) Bool (and (<= ab c)(= (+ (- a ab) b) 0)(= (+ (- a ac) c) 0)(= (- (- bc b) c) 0))) 
(define-fun evo ( (c Int)  (a Int)  (b Int)  (ac Int)  (ab Int)  (bc Int) ) Bool (and (<= ab c)(= (+ (- a ab) b) 0)(= (+ (- a ac) c) 0)(= (- (- bc b) c) 0)))

(push)
(assert (forall ( (c Int)  (a Int)  (b Int)  (ac Int)  (ab Int)  (bc Int) ) (=> (ours c a b ac ab bc) (evo c a b ac ab bc) )))
(check-sat)
(pop)

(push)
(assert (forall ( (c Int)  (a Int)  (b Int)  (ac Int)  (ab Int)  (bc Int) ) (=> (evo c a b ac ab bc) (ours c a b ac ab bc) )))
(check-sat)
(pop)
    