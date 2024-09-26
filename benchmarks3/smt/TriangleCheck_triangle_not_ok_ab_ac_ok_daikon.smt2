
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) Bool (and (>= a 1)(>= a bc)(> a b)(> a c)(> ab bc)(> ab b)(> ab c)(< bc ac)(< b ac)(> ac c)(= (+ (- a ab) b) 0)(= (+ (- a ac) c) 0)(= (- (- bc b) c) 0))) 
(define-fun evo ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) Bool (and (>= a 1)(>= a bc)(> a b)(> a c)(> ab bc)(> ab b)(> ab c)(< bc ac)(< b ac)(> ac c)(= (+ (- a ab) b) 0)(= (+ (- a ac) c) 0)(= (- (- bc b) c) 0)))

(push)
(assert (forall ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) (=> (ours c ac ab a b bc) (evo c ac ab a b bc) )))
(check-sat)
(pop)

(push)
(assert (forall ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) (=> (evo c ac ab a b bc) (ours c ac ab a b bc) )))
(check-sat)
(pop)
    