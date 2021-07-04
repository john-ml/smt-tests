; z3 4.8.0 segfaults, cvc4 returns unknown
(define-sort T (A) (Array A Bool))
(assert (forall ((s (T Int)) (t (T Int))) (= s t)))
(check-sat)
