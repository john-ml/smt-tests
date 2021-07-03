(declare-datatype MyList (par (A) ((my-cons (my-head A) (my-tail (MyList A))) (my-nil))))
(define-fun-rec my-append ((xs (MyList Int)) (ys (MyList Int))) (MyList Int)
  (match xs (
    ((my-cons x xs) (my-cons x (my-append xs ys)))
    (my-nil ys))))
(assert (forall ((xs (MyList Int))) (= (my-append xs my-nil) xs)))
(assert (forall ((xs (MyList Int)) (ys (MyList Int)) (zs (MyList Int)))
  (= (my-append xs (my-append ys zs)) (my-append (my-append xs ys) zs))))
(check-sat)
