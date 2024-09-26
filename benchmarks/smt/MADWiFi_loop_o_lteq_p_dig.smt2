
(set-logic ALL)
(define-fun min2 ((x Int) (y Int)) Int
    (ite (< x y) x y))
 
(define-fun max2 ((x Int) (y Int)) Int
    (ite (> x y) x y))
     
(define-fun-rec pow ((x Int) (n Int)) Int
    (ite (= n 0)
        1
        (* x (pow x (- n 1)))))

(define-fun ours ( (p Int) ) Bool (<= (- p) (- 2))) 
(define-fun evo ( (p Int) ) Bool (<= (- p) (- 2)))

(push)
(assert (forall ( (p Int) ) (=> (ours p) (evo p) )))
(check-sat)
(pop)

(push)
(assert (forall ( (p Int) ) (=> (evo p) (ours p) )))
(check-sat)
(pop)
    