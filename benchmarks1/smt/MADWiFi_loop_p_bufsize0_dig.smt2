
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (p Int)  (bufsize_0 Int) ) Bool (and (<= (- p) (- 2))(<= (- bufsize_0) (- 8))(<= (+ (- bufsize_0) p) 0))) 
(define-fun evo ( (p Int)  (bufsize_0 Int) ) Bool (<= (- p) (- 2)))

(push)
(assert (forall ( (p Int)  (bufsize_0 Int) ) (=> (ours p bufsize_0) (evo p bufsize_0) )))
(check-sat)
(pop)

(push)
(assert (forall ( (p Int)  (bufsize_0 Int) ) (=> (evo p bufsize_0) (ours p bufsize_0) )))
(check-sat)
(pop)
    