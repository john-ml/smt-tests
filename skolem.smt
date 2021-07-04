(set-logic ALL)

; ∀ x y, ¬ (x < y < x)
(push)
  (declare-const x Int)
  (declare-const y Int)
  (assert (< x y x))
  (check-sat)
(pop)

; ∀ f, (∀ x y, f x = f y → x = y) → f 3 = f 4 → 3 = 4
(push)
  (declare-fun f (Int) Int)
  (assert (forall ((x Int) (y Int)) (=> (= (f x) (f y)) (= x y))))
  (assert (= (f 3) (f 4)))
  (assert (not (= 3 4)))
  (check-sat)
(pop)

; ∀ A B (s : A → B) (x : A), s[x ← s[x]] = s
(push)
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-const s (Array A B))
  (declare-const x A)
  (assert (not (= (store s x (select s x)) s)))
  (check-sat)
(pop)

; ∀ A B (s : A → B) (x : A),
(push)
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-const s (Array A B))
  (declare-const x A)
  ; s[x ← s[x]] = s ∧
  (push)
    (assert (not (= (store s x (select s x)) s)))
    (check-sat)
  (pop)
  ; (∀ v, s[x ← v][x] = v) ∧
  (push)
    (declare-const v B)
    (assert (not (= (select (store s x v) x) v)))
    (check-sat)
  (pop)
  ; (∀ v w, s[x ← v][x ← w] = s[x ← w]) ∧
  (push)
    (declare-const v B)
    (declare-const w B)
    (assert (not (= (store (store s x v) x w) (store s x w))))
    (check-sat)
  (pop)
  ; (∀ v w, s[x ← v] = s[x ← w] → v = w)
  (push)
    (declare-const v B)
    (declare-const w B)
    (assert (= (store s x v) (store s x w)))
    (assert (not (= v w)))
    (check-sat)
  (pop)
(pop)

; ∀ A B C D,
(push)
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-sort C 0)
  (declare-sort D 0)
  ; let compose A B C (f : B → C) (g : A → B) : A → C = λx.f[g[x]] in
  ; (Explicitly monomorphized to ABC ACD ABD BCD),
  (declare-fun composeABC ((Array B C) (Array A B)) (Array A C))
  (declare-fun composeACD ((Array C D) (Array A C)) (Array A D))
  (declare-fun composeABD ((Array B D) (Array A B)) (Array A D))
  (declare-fun composeBCD ((Array C D) (Array B C)) (Array B D))
  (assert (forall ((f (Array B C)) (g (Array A B)) (x A))
    (= (select (composeABC f g) x) (select f (select g x)))))
  (assert (forall ((f (Array C D)) (g (Array A C)) (x A))
    (= (select (composeACD f g) x) (select f (select g x)))))
  (assert (forall ((f (Array B D)) (g (Array A B)) (x A))
    (= (select (composeABD f g) x) (select f (select g x)))))
  (assert (forall ((f (Array C D)) (g (Array B C)) (x B))
    (= (select (composeBCD f g) x) (select f (select g x)))))
  ; ∀ f g h,
  (declare-const f (Array C D))
  (declare-const g (Array B C))
  (declare-const h (Array A B))
  ; composeACD f (composeABC g h) = composeABD (composeBCD f g) h
  (assert (not
    (= (composeACD f (composeABC g h))
       (composeABD (composeBCD f g) h))))
  (check-sat)
(pop)

; ∀ A,
(push)
  (declare-sort A 0)
  ; let xs ∈ MyList ∷= [] | x ∷ xs in
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  ; let rec map f xs = ‥ in
  (define-fun-rec mymap ((f (Array A A)) (xs MyList)) MyList
    (match xs (
      (mynil mynil)
      ((mycons x xs) (mycons (select f x) (mymap f xs))))))
  ; let id : A → A = λx.x in
  (declare-const id (Array A A))
  (assert (forall ((x A)) (= (select id x) x)))
  ; Hangs: ∀ xs, map id xs = xs
  (push)
    (declare-const xs MyList)
    (assert (not (= (mymap id xs) xs)))
    ; (check-sat)
  (pop)
  ; Base case: map id [] = []
  (push) (assert (not (= (mymap id mynil) mynil))) (check-sat) (pop)
  ; Inductive case: ∀ x xs, map id xs = xs → map id (x ∷ xs) = x ∷ xs
  (push)
    (declare-const x A)
    (declare-const xs MyList)
    (assert (= (mymap id xs) xs))
    (assert (not (= (mymap id (mycons x xs)) (mycons x xs))))
    (check-sat)
  (pop)
  ; Strong inductive case: ∀ x xs, (∀ ys, |ys| < |xs| → map id ys = ys) → map id (x ∷ xs) = x ∷ xs
  (push)
    (declare-const x A)
    (declare-const xs MyList)
    (define-fun-rec len ((xs MyList)) Int
      (match xs (
        (mynil 0)
        ((mycons x xs) (+ 1 (len xs))))))
    (assert (forall ((ys MyList)) (=> (< (len ys) (len xs)) (= (mymap id ys) ys))))
    (assert (not (= (mymap id (mycons x xs)) (mycons x xs))))
    (check-sat)
  (pop)
(pop)

; Const arrays
(push)
  (declare-const s (Array Int Bool))
  (declare-fun f (Bool) Bool)
  (assert (= s ((as const (Array Int Bool)) false)))
  (assert (not (= (select s 0) false)))
  (check-sat)
(pop)

; Mapping over an array (z3 only)
#ifdef z3
(push)
  (declare-const s (Array Int Bool))
  (declare-fun f (Bool) Bool)
  (assert (select s 0))
  (assert (not (select s 1)))
  (assert (= ((_ map not) s) ((_ map f) s)))
  (check-sat)
  (get-model)
(pop)
#endif

; Sets (cvc4 only)
#ifndef z3
(push)
  (declare-const r (Set Int))
  (declare-const s (Set Int))
  (declare-const t (Set Int))
  (assert (not (= (union (union r s) t) (union r (union s t)))))
  (check-sat)
(pop)
#endif

; Can represent sets with maps into Bool:
(push)
  ; let MySet A = A → Bool in
  (define-sort MySet (A) (Array A Bool))
  ; let s ∪ t = λx. s[x] ∨ t[x] in
  (declare-fun cup ((MySet Int) (MySet Int)) (MySet Int))
  (assert (forall ((s (MySet Int)) (t (MySet Int)) (x Int))
    (= (select (cup s t) x) (or (select s x) (select t x)))))
  ; let s ∩ t = λx. s[x] ∧ t[x] in
  (declare-fun cap ((MySet Int) (MySet Int)) (MySet Int))
  (assert (forall ((s (MySet Int)) (t (MySet Int)) (x Int))
    (= (select (cap s t) x) (and (select s x) (select t x)))))
  ; let s \ t = λx. s[x] ∧ ¬t[x] in
  (declare-fun minus ((MySet Int) (MySet Int)) (MySet Int))
  (assert (forall ((s (MySet Int)) (t (MySet Int)) (x Int))
    (= (select (minus s t) x) (and (select s x) (not (select t x))))))
  ; ∀ (r s t : MySet Bool),
  (declare-const r (MySet Int))
  (declare-const s (MySet Int))
  (declare-const t (MySet Int))
  ; ((r ∪ s) ∪ t = r ∪ (s ∪ t)) ∧
  (push)
    (assert (not (= (cup (cup r s) t) (cup r (cup s t)))))
    (check-sat)
  (pop)
  ; ((r ∩ s) ∩ t = r ∩ (s ∩ t)) ∧
  (push)
    (assert (not (= (cap (cap r s) t) (cap r (cap s t)))))
    (check-sat)
  (pop)
  ; ((r ∪ s) ∩ t = (r ∩ t) ∪ (s ∩ t)) ∧
  (push)
    (assert (not (= (cap (cup r s) t) (cup (cap r t) (cap s t)))))
    (check-sat)
  (pop)
  ; (r ⊆ s → s ⊆ t → r ⊆ t) ∧
  (push)
    (assert (forall ((x Int)) (=> (select r x) (select s x))))
    (assert (forall ((x Int)) (=> (select s x) (select t x))))
    (declare-const x Int)
    (assert (select r x))
    (assert (not (select t x)))
    (check-sat)
  (pop)
  ; Alternatively, we can also define (⊆) as a predicate.
  ; let r ⊆ s = ∀ x. r[x] → s[x] in
  (define-fun subseteq ((s (MySet Int)) (t (MySet Int))) Bool
    (forall ((x Int)) (=> (select s x) (select t x))))
  ; (r ⊆ s → s ⊆ t → r ⊆ t) ∧
  (push)
    (assert (subseteq r s))
    (assert (subseteq s t))
    (assert (not (subseteq s t)))
    (check-sat)
  (pop)
  ; let s # t = λx. ¬ (s[x] ∧ t[x]) in
  (define-fun disjoint ((s (MySet Int)) (t (MySet Int))) Bool
    (forall ((x Int)) (not (and (select s x) (select t x)))))
  ; (s # t <=> t # s) ∧
  (push)
    (assert (not (= (disjoint s t) (disjoint t s))))
    (check-sat)
  (pop)
  ; ((s ∪ t) # r <=> (s # r) ∧ (t # r)) ∧
  (push)
    (assert (not (= (disjoint (cup s t) r) (and (disjoint s r) (disjoint t r)))))
    (check-sat)
  (pop)
  ; (∀ s t r, (s ∪ t) # r <=> (s # r) ∧ (t # r))
  (push)
    (assert (not
      (forall ((s (MySet Int)) (t (MySet Int)) (r (MySet Int)))
      (= (disjoint (cup s t) r) (and (disjoint s r) (disjoint t r))))))
    (check-sat)
  (pop)
  ; (∀ r s t u v, (r ∪ s ∪ t) # (u ∪ v) <=> r#u ∧ r#v ∧ s#u ∧ s#v ∧ t#u ∧ t#v)
  ; cvc4 can solve this but z3 segfaults
  #ifndef z3
  (push)
    (assert (not
      (forall ((r (MySet Int)) (s (MySet Int)) (t (MySet Int)) (u (MySet Int)) (v (MySet Int)))
      (= (disjoint (cup (cup r s) t) (cup u v))
         (and
           (disjoint r u)
           (disjoint r v)
           (disjoint s u)
           (disjoint s v)
           (disjoint t u)
           (disjoint t v)
    )))))
    (check-sat)
  (pop)
  #endif
(pop)

(push)
  ; ∀ A, let append (xs ys : list A) = .. in
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  (define-fun-rec append ((xs MyList) (ys MyList)) MyList
    (match xs (
      ((mycons x xs) (mycons x (append xs ys)))
      (mynil ys))))
  ; ∀ x xs ys, (x ∷ xs) ++ ys = x ∷ xs ++ ys
  (push)
    (assert (not
      (forall ((x A) (xs MyList) (ys MyList))
      (= (append (mycons x xs) ys) (mycons x (append xs ys))))))
    (check-sat)
  (pop)
  ; Hangs: ∀ xs ys zs, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  (push)
    (assert (not
      (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ; (check-sat)
  (pop)
  ; Base case: ∀ ys zs, ([] ++ ys) ++ zs = [] ++ (ys ++ zs)
  (push)
    (assert (not
      (forall ((ys MyList) (zs MyList))
      (= (append (append mynil ys) zs) (append mynil (append ys zs))))))
    (check-sat)
  (pop)
  ; Inductive case: ∀ x xs ys zs,
  ;   (xs ++ ys) ++ zs = xs ++ (ys ++ zs) →
  ;   ((x ∷ xs) ++ ys) ++ zs = (x ∷ xs) ++ (ys ++ zs) →
  (push)
    (assert (not
      (forall ((x A) (xs MyList) (ys MyList) (zs MyList)) (=>
      (= (append (append xs ys) zs) (append xs (append ys zs)))
      (= (append (append (mycons x xs) ys) zs) (append (mycons x xs) (append ys zs)))))))
  (check-sat)
  (pop)
  ; Can we prove the theorem given proofs of base and inductive cases?
  (push)
    (assert (forall ((ys MyList) (zs MyList))
      (= (append (append mynil ys) zs) (append mynil (append ys zs)))))
    (assert (forall ((x A) (xs MyList) (ys MyList) (zs MyList)) (=>
      (= (append (append xs ys) zs) (append xs (append ys zs)))
      (= (append (append (mycons x xs) ys) zs) (append (mycons x xs) (append ys zs))))))
    ; Both z3 and cvc4 hang.
    (assert (not
      (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ;(check-sat)
  (pop)
  ; Can we prove the theorem by induction given an induction scheme for lists?
  (push)
    ; ∀ ys zs,
    (declare-const ys MyList)
    (declare-const zs MyList)
    ; let f = λ xs. (xs ++ ys) ++ zs = xs ++ (ys ++ zs) in
    ; (Because SMT is first-order, need to stuff the predicate into an Array)
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList))
      (= (select f xs) (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ; Base case provable with this new representation of the predicate:
    (push)
      (assert (not (select f mynil)))
      (check-sat)
    (pop)
    ; Inductive case too:
    ; (∀ x xs, f[xs] → f[x ∷ xs]) ∧
    (push)
      (assert (not (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))))
      (check-sat)
    (pop)
    ; But main theorem not provable (both z3 and cvc4 hang):
    ; (∀ xs, f[xs])
    (push)
      (assert (not (forall ((xs MyList)) (select f xs))))
      ;(check-sat)
    (pop)
    ; Assume standard induction principle for lists:
    ; (∀ (f : List A → Bool) xs,
    ;   f[[]] →
    ;   (∀ x xs, f[xs] → f[x ∷ xs]) →
    ;   f[xs]) →
    (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
      (select f mynil)
      (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
      (select f xs))))
    ; Now, both solvers can prove ∀ xs, f[xs]
    (push) (assert (not (forall ((xs MyList)) (select f xs)))) (check-sat) (pop)
  (pop)
  ; Could also define f as a function in this case because induction only used once:
  (push)
    ; ∀ f ys zs,
    (declare-const ys MyList)
    (declare-const zs MyList)
    ; f xs <=> (xs ++ ys) ++ zs = xs ++ (ys ++ zs) →
    (define-fun f ((xs MyList)) Bool
      (= (append (append xs ys) zs) (append xs (append ys zs))))
    ; Base case provable with this new representation of the predicate:
    (push)
      (assert (not (f mynil)))
      (check-sat)
    (pop)
    ; Inductive case too:
    ; (∀ x xs, f xs → f (x ∷ xs)) ∧
    (push)
      (assert (not (forall ((x A) (xs MyList)) (=> (f xs) (f (mycons x xs))))))
      (check-sat)
    (pop)
    ; But main theorem not provable (both z3 and cvc4 hang):
    ; (∀ xs, f xs)
    (push)
      (assert (not (forall ((xs MyList)) (f xs))))
      ;(check-sat)
    (pop)
    ; Assume standard induction principle for lists:
    ; (∀ (f : List A → Bool) xs,
    ;   f[[]] →
    ;   (∀ x xs, f[xs] → f[x ∷ xs]) →
    ;   f[xs]) →
    (assert (forall ((xs MyList)) (=>
      (f mynil)
      (forall ((x A) (xs MyList)) (=> (f xs) (f (mycons x xs))))
      (f xs))))
    ; Now, both solvers can prove ∀ xs, f xs
    (push) (assert (not (forall ((xs MyList)) (f xs)))) (check-sat) (pop)
  (pop)
  ; If just assert append-assoc theorem and check for sat,
  ; z3 can prove it but cvc4 returns unknown
  (push)
    (assert (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs)))))
    (check-sat)
  (pop)
(pop)

; So z3 somehow "knows" about induction.
; But it fails to prove the standard induction principle for lists:
; ∀ A (f : List A → bool),
(push)
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  (declare-fun f (MyList) Bool)
  ; f [] →
  (assert (f mynil))
  ; (∀ x xs, f xs → f (x ∷ xs)) →
  (assert (forall ((x A) (xs MyList)) (=> (f xs) (f (mycons x xs)))))
  ; z3 hangs, cvc4 returns unknown: ∀ xs, f xs
  (assert (not (forall ((xs MyList)) (f xs))))
  ;(check-sat)
(pop)

; Does not help if we try to prove it by asserting it and checking for sat:
(push)
  (declare-datatype IntList ((mynil) (mycons (head Int) (tail IntList))))
  (declare-fun f (IntList) Bool)
  (assert (forall ((f (Array IntList Bool)) (xs IntList)) (=>
    (select f mynil)
    (forall ((x Int) (xs IntList)) (=> (select f xs) (select f (mycons x xs))))
    (select f xs))))
  (check-sat) ; both solvers return unknown
(pop)

(push)
  ; ∀ A B C,
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-sort C 0)
  (declare-datatype Prod (par (D E) ((pair (fst D) (snd E)))))
  ; let curry (f : A × B → C) : A → B → C = λ x y. f[(x, y)] in
  ; let uncurry (f : A → B → C) : A × B → C = λ (x, y). f[x][y] in
  (declare-fun curry ((Array (Prod A B) C)) (Array A (Array B C)))
  (declare-fun uncurry ((Array A (Array B C))) (Array (Prod A B) C))
  (assert (forall ((f (Array (Prod A B) C)) (x A) (y B))
    (= (select (select (curry f) x) y) (select f (pair x y)))))
  (assert (forall ((f (Array A (Array B C))) (x A) (y B))
    (= (select (select f x) y) (select (uncurry f) (pair x y)))))
  ; ((∀ f, curry (uncurry f) = f) ∧ (∀ f, curry (uncurry f) = f)) ∧
  (push)
    (assert (not
      (and
        (forall ((f (Array A (Array B C)))) (= (curry (uncurry f)) f))
        (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f)))))
    (check-sat) ; z3 solves it, cvc4 returns unknown
  (pop)
  ; (∀ f, curry (uncurry f) = f) ∧
  (push)
    (assert (not (forall ((f (Array A (Array B C)))) (= (curry (uncurry f)) f))))
    (check-sat)
  (pop)
  ; (∀ f, curry (uncurry f) = f) ∧
  (push)
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    (check-sat) ; z3 solves it, cvc4 returns unknown
  (pop)
  ; If we state the definition of uncurry slightly different, cvc4 gets it
  (push)
    (assert (forall ((f (Array A (Array B C))) (xy (Prod A B)))
      (= (select (select f (fst xy)) (snd xy)) (select (uncurry f) xy))))
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    (check-sat)
  (pop)
  ; The eta law for pairs is not enough for cvc4
  (push)
    (assert (forall ((xy (Prod A B))) (= xy (pair (fst xy) (snd xy)))))
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    (check-sat)
  (pop)
  ; Nor is explicitly applying (uncurry (curry f)) and f to arguments
  (push)
    (assert (not (forall ((f (Array (Prod A B) C)) (xy (Prod A B)))
      (= (select (uncurry (curry f)) xy) (select f xy)))))
    (check-sat)
  (pop)
  ; But if we explicitly apply (uncurry (curry f)) to pairs (x, y), then it gets it
  (push)
    (assert (not (forall ((f (Array (Prod A B) C)) (x A) (y B))
      (= (select (uncurry (curry f)) (pair x y)) (select f (pair x y))))))
    (check-sat)
  (pop)
(pop)
