(push 1)
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  ; let append (xs ys : list A) = ‥ in
  (define-fun-rec append ((xs MyList) (ys MyList)) MyList
    (match xs (
      ((mycons x xs) (mycons x (append xs ys)))
      (mynil ys))))
  ; let reverse (xs : list A) = ‥ in
  (define-fun-rec reverse ((xs MyList)) MyList
    (match xs (
      ((mycons x xs) (append xs (mycons x mynil)))
      (mynil mynil))))
  ; Induction principle
  (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
    (select f mynil)
    (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
    (select f xs))))
  ; ∀ xs, xs ++ [] = xs
  (push 1)
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList)) (= (select f xs) (= (append xs mynil) xs))))
    (assert (not (forall ((xs MyList)) (select f xs))))
    (check-sat)
  (pop 1)
  (assert (forall ((xs MyList)) (= (append xs mynil) xs)))
  ; ∀ xs ys zs, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  (push 1)
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList)) (= (select f xs)
      (forall ((ys MyList) (zs MyList))
        (= (append (append xs ys) zs) (append xs (append ys zs)))))))
    (push 1)
    (assert (not (forall ((xs MyList)) (select f xs))))
    (check-sat)
    (pop 1)
  (pop 1)
  (assert (forall ((xs MyList) (ys MyList) (zs MyList))
    (= (append (append xs ys) zs) (append xs (append ys zs)))))
  ; Solvers can't prove
  ; ∀ xs, rev (xs ++ ys) = rev ys ++ rev xs
  (push 1)
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList)) (= (select f xs)
      (forall ((ys MyList)) (= (reverse (append xs ys)) (append (reverse ys) (reverse xs)))))))
    (assert (not (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))))
    ;(assert (not (forall ((xs MyList)) (select f xs))))
    ;(check-sat)
  (pop 1)
(pop 1)

; Also works fine to define append manually without using define-fun-rec
(push 1)
  ; ∀ A, let append (xs ys : list A) = ‥ in
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  (declare-fun append (MyList MyList) MyList)
  (assert (forall ((xs MyList) (ys MyList))
    (= (append xs ys) (match xs (((mycons x xs) (mycons x (append xs ys))) (mynil ys))))))
  ; ∀ x xs ys, (x ∷ xs) ++ ys = x ∷ xs ++ ys
  (push 1)
    (assert (not
      (forall ((x A) (xs MyList) (ys MyList))
      (= (append (mycons x xs) ys) (mycons x (append xs ys))))))
    (check-sat)
  (pop 1)
  ; Hangs: ∀ xs ys zs, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  (push 1)
    (assert (not
      (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ;(check-sat)
  (pop 1)
  ; Base case: ∀ ys zs, ([] ++ ys) ++ zs = [] ++ (ys ++ zs)
  (push 1)
    (assert (not
      (forall ((ys MyList) (zs MyList))
      (= (append (append mynil ys) zs) (append mynil (append ys zs))))))
    (check-sat)
  (pop 1)
  ; Inductive case: ∀ x xs ys zs,
  ;   (xs ++ ys) ++ zs = xs ++ (ys ++ zs) →
  ;   ((x ∷ xs) ++ ys) ++ zs = (x ∷ xs) ++ (ys ++ zs) →
  (push 1)
    (assert (not
      (forall ((x A) (xs MyList) (ys MyList) (zs MyList)) (=>
      (= (append (append xs ys) zs) (append xs (append ys zs)))
      (= (append (append (mycons x xs) ys) zs) (append (mycons x xs) (append ys zs)))))))
  (check-sat)
  (pop 1)
  ; Can we prove the theorem given proofs of base and inductive cases?
  (push 1)
    (assert (forall ((ys MyList) (zs MyList))
      (= (append (append mynil ys) zs) (append mynil (append ys zs)))))
    (assert (forall ((x A) (xs MyList) (ys MyList) (zs MyList)) (=>
      (= (append (append xs ys) zs) (append xs (append ys zs)))
      (= (append (append (mycons x xs) ys) zs) (append (mycons x xs) (append ys zs))))))
    ; All solvers hang.
    (assert (not
      (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ;(check-sat)
  (pop 1)
  ; Can we prove the theorem by induction given an induction scheme for lists?
  (push 1)
    ; ∀ ys zs,
    (declare-const ys MyList)
    (declare-const zs MyList)
    ; let f = λ xs. (xs ++ ys) ++ zs = xs ++ (ys ++ zs) in
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList))
      (= (select f xs) (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ; Assume standard induction principle for lists:
    ; (∀ (f : List A → Bool) xs,
    ;   f[[]] →
    ;   (∀ x xs, f[xs] → f[x ∷ xs]) →
    ;   f[xs]) →
    (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
      (select f mynil)
      (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
      (select f xs))))
    ; Proof
    (push 1) (assert (not (forall ((xs MyList)) (select f xs)))) (check-sat) (pop 1)
  (pop 1)
(pop 1)
