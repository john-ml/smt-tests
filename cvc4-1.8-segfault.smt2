(declare-datatype Box (par (A) ((box (unbox A)))))
(assert (forall ((xy (Box Bool))) (unbox xy)))
(check-sat)