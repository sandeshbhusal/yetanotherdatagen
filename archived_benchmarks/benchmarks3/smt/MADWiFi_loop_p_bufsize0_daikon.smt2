
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (bufsize_0 Int)  (p Int) ) Bool (and (>= p 2)(<= p bufsize_0))) 
(define-fun evo ( (bufsize_0 Int)  (p Int) ) Bool true)

(push)
(assert (forall ( (bufsize_0 Int)  (p Int) ) (=> (ours bufsize_0 p) (evo bufsize_0 p) )))
(check-sat)
(pop)

(push)
(assert (forall ( (bufsize_0 Int)  (p Int) ) (=> (evo bufsize_0 p) (ours bufsize_0 p) )))
(check-sat)
(pop)
    