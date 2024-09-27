
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) Bool (and (= (+ (- b bc) c) 0)(= (+ (- a ac) c) 0)(= (+ (- (- ab ac) bc) (* 2 c)) 0)(<= (+ (- a) bc) 0)(<= (+ (- ab) c) (- 1))(<= (+ (- ac) b) (- 1)))) 
(define-fun evo ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) Bool (and (= (+ (- a ac) c) 0)(= (+ (- b bc) c) 0)(= (+ (- (- ab ac) bc) (* 2 c)) 0)(<= (+ (- a) bc) 0)(<= (+ (- ab) c) (- 1))(<= (+ (- ac) b) (- 1))))

(push)
(assert (forall ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) (=> (ours c ac ab a b bc) (evo c ac ab a b bc) )))
(check-sat)
(pop)

(push)
(assert (forall ( (c Int)  (ac Int)  (ab Int)  (a Int)  (b Int)  (bc Int) ) (=> (evo c ac ab a b bc) (ours c ac ab a b bc) )))
(check-sat)
(pop)
    