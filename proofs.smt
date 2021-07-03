(set-option :produce-proofs true)
(push)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (distinct p q r))
(check-sat)
(get-proof)
(pop)

(push)
(define-fun-rec append ((xs (List Int)) (ys (List Int))) (List Int)
  (match xs (
    ((insert x xs) (insert x (append xs ys)))
    (nil ys))))
(declare-const xs (List Int))
; Times out
; (assert (not (= (append xs nil) xs)))
(assert (not (= (append nil xs) xs)))
(check-sat)
(get-proof)
(pop)

; Interestingly, if I first assert (∀ xs, xs ++ [] == xs) (which z3 can somehow prove),
; then I can get a proof out...
(push)
(define-fun-rec append ((xs (List Int)) (ys (List Int))) (List Int)
  (match xs (
    ((insert x xs) (insert x (append xs ys)))
    (nil ys))))
(assert (forall ((xs (List Int))) (= (append xs nil) xs)))
(declare-const xs (List Int))
(assert (not (= (append xs nil) xs)))
(check-sat)
(get-proof) ; ...but I don't see any kind of induction argument being made in the proof
(pop)
