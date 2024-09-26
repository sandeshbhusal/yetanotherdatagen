
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (bc Int)  (a Int)  (ab Int)  (b Int)  (c Int)  (ac Int) ) Bool (and (= (+ (- b bc) c) 0)(= (+ (- a ac) c) 0)(= (+ (- (- ab ac) bc) (* 2 c)) 0)(<= (- ac b) 0)(<= (+ (- ab) c) (- 1)))) 
(define-fun evo ( (bc Int)  (a Int)  (ab Int)  (b Int)  (c Int)  (ac Int) ) Bool (and (= (+ (- a ac) c) 0)(= (+ (- b bc) c) 0)(= (+ (- (- ab ac) bc) (* 2 c)) 0)(<= (- ac b) 0)(<= (+ (- ab) c) (- 1))))

(push)
(assert (forall ( (bc Int)  (a Int)  (ab Int)  (b Int)  (c Int)  (ac Int) ) (=> (ours bc a ab b c ac) (evo bc a ab b c ac) )))
(check-sat)
(pop)

(push)
(assert (forall ( (bc Int)  (a Int)  (ab Int)  (b Int)  (c Int)  (ac Int) ) (=> (evo bc a ab b c ac) (ours bc a ab b c ac) )))
(check-sat)
(pop)
    