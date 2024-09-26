
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (r Int)  (a Int)  (b Int)  (q Int) ) Bool (and (= (- (- a (* b q)) r) 0)(<= (- q) 0)(<= (- b r) 0)(<= (+ (- a) b) 0))) 
(define-fun evo ( (r Int)  (a Int)  (b Int)  (q Int) ) Bool (and (= (- (- a (* b q)) r) 0)(<= (- q) 0)(<= (- b r) 0)(<= (+ (- a) b) 0)))

(push)
(assert (forall ( (r Int)  (a Int)  (b Int)  (q Int) ) (=> (ours r a b q) (evo r a b q) )))
(check-sat)
(pop)

(push)
(assert (forall ( (r Int)  (a Int)  (b Int)  (q Int) ) (=> (evo r a b q) (ours r a b q) )))
(check-sat)
(pop)
    