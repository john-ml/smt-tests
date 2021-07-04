(set-logic ALL)
(declare-datatype Box (par (A) ((box (unbox A)))))
(define-fun box-fun ((x Int)) (Box Int) (box x))
(define-fun unbox-fun ((x (Box Int))) Int (match x (((box x) x))))
(assert (forall ((x Int)) (= (box-fun x) (box x))))
(assert (forall ((x (Box Int))) (= (unbox-fun x) (unbox x))))
(assert (forall ((x (Box Int))) (= (box-fun (unbox-fun x)) x)))
(assert (forall ((x Int)) (= (unbox-fun (box-fun x)) x)))
(check-sat)