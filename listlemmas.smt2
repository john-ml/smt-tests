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

; Bizarrely, this hangs
(push)
(assert (forall ((x Int) (xs (List Int)) (ys (List Int)))
  (= (append (insert x xs) ys) (insert x (append xs ys)))))
;(check-sat)
(pop)

(push)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= (append (insert 1 (insert 2 nil)) (insert 3 nil)) (insert a (insert b (insert c nil)))))
(check-sat)
(get-model)
(pop)

(define-fun-rec length ((xs (List Int))) Int
  (match xs (
    ((insert x xs) (+ 1 (length xs)))
    (nil 0))))

(push)
(assert (forall ((xs (List Int)) (ys (List Int)))
  (= (length (append xs ys)) (+ (length xs) (length ys)))))
(check-sat)
(pop)

(push)
(assert (forall ((xs (List Int)) (ys (List Int)))
  (= (length (append xs ys)) (length (append ys xs)))))
(check-sat)
(pop)

(push)
(assert (forall ((xs (List Int)) (ys (List Int)))
  (= (length (reverse xs)) (length xs))))
(check-sat)
(pop)

; Returns unknown...
(push)
(assert (forall ((xs (List Int)) (ys (List Int)))
  (= (reverse (append xs ys)) (append (reverse ys) (reverse xs)))))
(check-sat)
(pop)

; But if you assert the base and inductive cases, it solves it!
(push)
(assert (forall ((ys (List Int)))
  (= (reverse (append nil ys)) (append (reverse nil) (reverse ys)))))
(check-sat) ; but you need (check-sat) for each auxiliary lemma to guide it; otherwise, it hangs
(assert (forall ((x Int) (xs (List Int)) (ys (List Int)))
  (or
    (not (= (reverse (append xs ys)) (append (reverse xs) (reverse ys))))
    (= (reverse (append (insert x xs) ys)) (append (reverse (insert x xs)) (reverse ys))))))
(check-sat)
(assert (forall ((xs (List Int)) (ys (List Int)))
  (= (reverse (append xs ys)) (append (reverse xs) (reverse ys)))))
(check-sat)
(pop)
