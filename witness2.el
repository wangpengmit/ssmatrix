(trace 
 (name ex1)
 (from (+ (* 2 a) (* a 4)))
 ;; can have line comment
 (trans
  (rewrite mulrC (* a 4))
  (rewrite -mulrDl (+ (* 2 a) (* 4 a)))
  (fold (- 2 4) 6))
 (to (* 6 a)))
