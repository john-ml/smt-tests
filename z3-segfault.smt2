; z3 segfaults, cvc4 returns unknown
(define-sort Set (A) (Array A Bool))
(assert (forall ((s (Set Int)) (t (Set Int))) (= s t)))
(check-sat)
