(trace 
 (name ex1)
 (from (+ (* 2 a) (* a 4)))
 ;; can have line comment
 (trans
  (rewrite mulrC (* a 4))
  (rewrite -mulrDl (+ (* 2 a) (* 4 a)))
  (fold (+ 2 4) 6))
 (to (* 6 a)))

(trace
 (name ex2)
 (from (+ (^ (- a a) 2) (- a a)))
 (trans
  (lift (- a a))
  (rewrite addrN (- a a))
  beta
  (fold (+ (^ 0 2) 0) 0))
 (to 0))

(trace
 (name ex3)
 (from (/ a a))
 (trans
  (rewrite divrr (/ a a)))
 (to 1))
