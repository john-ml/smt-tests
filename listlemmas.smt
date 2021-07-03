(define-fun-rec append ((xs (List Int)) (ys (List Int))) (List Int)
  (match xs (
    ((insert x xs) (insert x (append xs ys)))
    (nil ys))))
(define-fun-rec reverse ((xs (List Int))) (List Int)
  (match xs (
    ((insert x xs) (append (reverse xs) (insert x nil)))
    (nil nil))))

; Interestingly, z3 hangs if I don't push/pop to isolate the associativity proof from the
; test case rev [1, 2, 3] = [3, 2, 1].
; Using (get-model) and C-c to interrupt the solver reveals that its model of append seems
; to blow up with ites involving the list [1, 2, 3]

(push)
(assert (forall ((xs (List Int)) (ys (List Int)) (zs (List Int)))
  (= (append xs (append ys zs)) (append (append xs ys) zs))))
(check-sat)
(pop)

(push)
(assert (forall ((xs (List Int))) (= (append xs nil) xs)))
(check-sat)
(pop)

(push)
(assert (= (reverse (insert 1 (insert 2 (insert 3 nil)))) (insert 3 (insert 2 (insert 1 nil)))))
(check-sat)
(pop)
