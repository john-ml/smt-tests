(set-logic ALL)

; ∀ x y, ¬ (x < y < x)
(push 1)
  (declare-const x Int)
  (declare-const y Int)
  (assert (< x y x))
  (check-sat)
(pop 1)

; ∀ f, (∀ x y, f x = f y → x = y) → f 3 = f 4 → 3 = 4
(push 1)
  (declare-fun f (Int) Int)
  (assert (forall ((x Int) (y Int)) (=> (= (f x) (f y)) (= x y))))
  (assert (= (f 3) (f 4)))
  (assert (not (= 3 4)))
  (check-sat)
(pop 1)

; ∀ A B (s : A → B) (x : A), s[x ← s[x]] = s
(push 1)
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-const s (Array A B))
  (declare-const x A)
  (assert (not (= (store s x (select s x)) s)))
  (check-sat)
(pop 1)

; ∀ A B (s : A → B) (x : A),
(push 1)
  (declare-sort A 0)
  (declare-sort B 0)
  (declare-const s (Array A B))
  (declare-const x A)
  ; s[x ← s[x]] = s ∧
  (push 1)
    (assert (not (= (store s x (select s x)) s)))
    (check-sat)
  (pop 1)
  ; (∀ v, s[x ← v][x] = v) ∧
  (push 1)
    (declare-const v B)
    (assert (not (= (select (store s x v) x) v)))
    (check-sat)
  (pop 1)
  ; (∀ v w, s[x ← v][x ← w] = s[x ← w]) ∧
  (push 1)
    (declare-const v B)
    (declare-const w B)
    (assert (not (= (store (store s x v) x w) (store s x w))))
    (check-sat)
  (pop 1)
  ; (∀ v w, s[x ← v] = s[x ← w] → v = w)
  (push 1)
    (declare-const v B)
    (declare-const w B)
    (assert (= (store s x v) (store s x w)))
    (assert (not (= v w)))
    (check-sat)
  (pop 1)
(pop 1)

; ∀ A B C D,
(push 1)
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
(pop 1)

; ∀ A,
(push 1)
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
  (push 1)
    (declare-const xs MyList)
    (assert (not (= (mymap id xs) xs)))
    ; (check-sat)
  (pop 1)
  ; Base case: map id [] = []
  (push 1) (assert (not (= (mymap id mynil) mynil))) (check-sat) (pop 1)
  ; Inductive case: ∀ x xs, map id xs = xs → map id (x ∷ xs) = x ∷ xs
  (push 1)
    (declare-const x A)
    (declare-const xs MyList)
    (assert (= (mymap id xs) xs))
    (assert (not (= (mymap id (mycons x xs)) (mycons x xs))))
    (check-sat)
  (pop 1)
  ; Strong inductive case: ∀ x xs, (∀ ys, |ys| < |xs| → map id ys = ys) → map id (x ∷ xs) = x ∷ xs
  (push 1)
    (declare-const x A)
    (declare-const xs MyList)
    (define-fun-rec len ((xs MyList)) Int
      (match xs (
        (mynil 0)
        ((mycons x xs) (+ 1 (len xs))))))
    (assert (forall ((ys MyList)) (=> (< (len ys) (len xs)) (= (mymap id ys) ys))))
    (assert (not (= (mymap id (mycons x xs)) (mycons x xs))))
    (check-sat)
  (pop 1)
(pop 1)

; Const arrays
#ifndef alt_ergo
(push 1)
  (declare-const s (Array Int Bool))
  (declare-fun f (Bool) Bool)
  (assert (= s ((as const (Array Int Bool)) false)))
  (assert (not (= (select s 0) false)))
  (check-sat)
(pop 1)
#endif

; Mapping over an array (z3 only)
#ifdef z3
(push 1)
  (declare-const s (Array Int Bool))
  (declare-fun f (Bool) Bool)
  (assert (select s 0))
  (assert (not (select s 1)))
  (assert (= ((_ map not) s) ((_ map f) s)))
  (check-sat)
  (get-model)
(pop 1)
#endif

; Sets
#ifndef alt_ergo
(push 1)
  (declare-const r (Set Int))
  (declare-const s (Set Int))
  (declare-const t (Set Int))
  (assert (not (= (union (union r s) t) (union r (union s t)))))
  (check-sat)
(pop 1)
#endif

; Can represent sets with maps into Bool:
(push 1)
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
  (push 1)
    (assert (not (= (cup (cup r s) t) (cup r (cup s t)))))
    (check-sat)
  (pop 1)
  ; ((r ∩ s) ∩ t = r ∩ (s ∩ t)) ∧
  (push 1)
    (assert (not (= (cap (cap r s) t) (cap r (cap s t)))))
    (check-sat)
  (pop 1)
  ; ((r ∪ s) ∩ t = (r ∩ t) ∪ (s ∩ t)) ∧
  (push 1)
    (assert (not (= (cap (cup r s) t) (cup (cap r t) (cap s t)))))
    (check-sat)
  (pop 1)
  ; (r ⊆ s → s ⊆ t → r ⊆ t) ∧
  (push 1)
    (assert (forall ((x Int)) (=> (select r x) (select s x))))
    (assert (forall ((x Int)) (=> (select s x) (select t x))))
    (declare-const x Int)
    (assert (select r x))
    (assert (not (select t x)))
    (check-sat)
  (pop 1)
  ; Alternatively, we can also define (⊆) as a predicate.
  ; let r ⊆ s = ∀ x. r[x] → s[x] in
  (define-fun subseteq ((s (MySet Int)) (t (MySet Int))) Bool
    (forall ((x Int)) (=> (select s x) (select t x))))
  ; (r ⊆ s → s ⊆ t → r ⊆ t) ∧
  (push 1)
    (assert (subseteq r s))
    (assert (subseteq s t))
    (assert (not (subseteq s t)))
    (check-sat)
  (pop 1)
  ; let s # t = λx. ¬ (s[x] ∧ t[x]) in
  (define-fun disjoint ((s (MySet Int)) (t (MySet Int))) Bool
    (forall ((x Int)) (not (and (select s x) (select t x)))))
  ; (s # t <=> t # s) ∧
  (push 1)
    (assert (not (= (disjoint s t) (disjoint t s))))
    (check-sat)
  (pop 1)
  ; ((s ∪ t) # r <=> (s # r) ∧ (t # r)) ∧
  (push 1)
    (assert (not (= (disjoint (cup s t) r) (and (disjoint s r) (disjoint t r)))))
    (check-sat)
  (pop 1)
  ; (∀ s t r, (s ∪ t) # r <=> (s # r) ∧ (t # r))
  (push 1)
    (assert (not
      (forall ((s (MySet Int)) (t (MySet Int)) (r (MySet Int)))
      (= (disjoint (cup s t) r) (and (disjoint s r) (disjoint t r))))))
    (check-sat)
  (pop 1)
  ; (∀ r s t u v, (r ∪ s ∪ t) # (u ∪ v) <=> r#u ∧ r#v ∧ s#u ∧ s#v ∧ t#u ∧ t#v)
  ; cvc4 and alt-ergo can solve this but z3 returns unknown
  (push 1)
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
  (pop 1)
(pop 1)

(push 1)
  ; ∀ A, let append (xs ys : list A) = ‥ in
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  (define-fun-rec append ((xs MyList) (ys MyList)) MyList
    (match xs (
      ((mycons x xs) (mycons x (append xs ys)))
      (mynil ys))))
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
    ; (Because SMT is first-order, need to stuff the predicate into an Array)
    (declare-const f (Array MyList Bool))
    (assert (forall ((xs MyList))
      (= (select f xs) (= (append (append xs ys) zs) (append xs (append ys zs))))))
    ; Base case provable with this new representation of the predicate:
    (push 1)
      (assert (not (select f mynil)))
      (check-sat)
    (pop 1)
    ; Inductive case too:
    ; (∀ x xs, f[xs] → f[x ∷ xs]) ∧
    (push 1)
      (assert (not (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))))
      (check-sat)
    (pop 1)
    ; But main theorem not provable (all provers hang):
    ; (∀ xs, f[xs])
    (push 1)
      (assert (not (forall ((xs MyList)) (select f xs))))
      ;(check-sat)
    (pop 1)
    ; Assume standard induction principle for lists:
    ; (∀ (f : List A → Bool) xs,
    ;   f[[]] →
    ;   (∀ x xs, f[xs] → f[x ∷ xs]) →
    ;   f[xs]) →
    (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
      (select f mynil)
      (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
      (select f xs))))
    ; Now, cvc4 and alt-ergo can prove ∀ xs, f[xs] (z3 hangs)
    #ifndef z3
    (push 1) (assert (not (forall ((xs MyList)) (select f xs)))) (check-sat) (pop 1)
    #endif
  (pop 1)
  ; Could also define f as a function in this case because induction only used once:
  (push 1)
    ; ∀ f ys zs,
    (declare-const ys MyList)
    (declare-const zs MyList)
    ; f xs <=> (xs ++ ys) ++ zs = xs ++ (ys ++ zs) →
    (define-fun f ((xs MyList)) Bool
      (= (append (append xs ys) zs) (append xs (append ys zs))))
    ; Base case provable with this new representation of the predicate:
    (push 1)
      (assert (not (f mynil)))
      (check-sat)
    (pop 1)
    ; Inductive case too:
    ; (∀ x xs, f xs → f (x ∷ xs)) ∧
    (push 1)
      (assert (not (forall ((x A) (xs MyList)) (=> (f xs) (f (mycons x xs))))))
      (check-sat)
    (pop 1)
    ; But main theorem not provable (all provers hang):
    ; (∀ xs, f xs)
    (push 1)
      (assert (not (forall ((xs MyList)) (f xs))))
      ;(check-sat)
    (pop 1)
    ; Assume standard induction principle for lists:
    ; (∀ (f : List A → Bool) xs,
    ;   f[[]] →
    ;   (∀ x xs, f[xs] → f[x ∷ xs]) →
    ;   f[xs]) →
    (assert (forall ((xs MyList)) (=>
      (f mynil)
      (forall ((x A) (xs MyList)) (=> (f xs) (f (mycons x xs))))
      (f xs))))
    ; Now, cvc4 and alt-ergo can prove ∀ xs, f xs (z3 hangs)
    #ifndef z3
    (push 1) (assert (not (forall ((xs MyList)) (f xs)))) (check-sat) (pop 1)
    #endif
  (pop 1)
  ; If just assert append-assoc theorem and check for sat,
  ; z3 hangs, cvc4 and alt-ergo return unknown
  #ifndef z3
  (push 1)
    (assert (forall ((xs MyList) (ys MyList) (zs MyList))
      (= (append (append xs ys) zs) (append xs (append ys zs)))))
    (check-sat)
  (pop 1)
  #endif
(pop 1)

(push 1)
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
  (push 1)
    (assert (not
      (and
        (forall ((f (Array A (Array B C)))) (= (curry (uncurry f)) f))
        (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f)))))
    (check-sat) ; z3 solves it, cvc4 returns unknown, cvc4-1.8 solves it, alt-ergo solves it
  (pop 1)
  ; (∀ f, curry (uncurry f) = f) ∧
  (push 1)
    (assert (not (forall ((f (Array A (Array B C)))) (= (curry (uncurry f)) f))))
    (check-sat)
  (pop 1)
  ; (∀ f, curry (uncurry f) = f) ∧
  (push 1)
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    (check-sat) ; z3 solves it, cvc4 returns unknown, cvc4-1.8 solves it
  (pop 1)
  ; If we state the definition of uncurry slightly differently, cvc4 (1.6) solves it
  (push 1)
    (assert (forall ((f (Array A (Array B C))) (xy (Prod A B)))
      (= (select (select f (fst xy)) (snd xy)) (select (uncurry f) xy))))
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    #ifndef cvc4_1_8
    (check-sat) ; cvc4-1.8 segfaults!
    #endif
  (pop 1)
  ; Can we spell it out for cvc4-1.6 without using an alternate definition of uncurry?
  ; The eta law for pairs is not enough:
  (push 1)
    (assert (forall ((xy (Prod A B))) (= xy (pair (fst xy) (snd xy)))))
    (assert (not (forall ((f (Array (Prod A B) C))) (= (uncurry (curry f)) f))))
    #ifndef cvc4_1_8
    (check-sat) ; cvc4-1.8 emits a mysterious error message ("Datatype type not fully instantiated")
    #endif
  (pop 1)
  ; Nor is explicitly applying (uncurry (curry f)) and f to arguments
  (push 1)
    (assert (not (forall ((f (Array (Prod A B) C)) (xy (Prod A B)))
      (= (select (uncurry (curry f)) xy) (select f xy)))))
    (check-sat)
  (pop 1)
  ; If we explicitly apply (uncurry (curry f)) to pairs (x, y), then cvc4 1.6 solves it
  (push 1)
    (assert (not (forall ((f (Array (Prod A B) C)) (x A) (y B))
      (= (select (uncurry (curry f)) (pair x y)) (select f (pair x y))))))
    (check-sat)
  (pop 1)
  ; But then given this expanded fact as assumption, it cannot prove the theorem
  (push 1)
    (assert (forall ((f (Array (Prod A B) C)) (x A) (y B))
      (= (select (uncurry (curry f)) (pair x y)) (select f (pair x y)))))
    (assert (not (forall ((f (Array (Prod A B) C)) (xy (Prod A B)))
      (= (select (uncurry (curry f)) xy) (select f xy)))))
    (check-sat)
  (pop 1)
(pop 1)

(push 1)
  ; ∀ A,
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  ; ∀ (∈),
  (declare-fun contains (A MyList) Bool)
  ; (∀ x, x ∉ []) →
  (assert (forall ((x A)) (not (contains x mynil))))
  ; (∀ x xs, x ∈ x ∷ xs) →
  (assert (forall ((x A) (xs MyList)) (contains x (mycons x xs))))
  ; (∀ x y xs, x ≠ y → x ∈ xs → x ∈ y ∷ xs) →
  (assert (forall ((x A) (y A) (xs MyList)) (=>
    (distinct x y)
    (contains x xs)
    (contains x (mycons y xs)))))
  ; (∀ x, x ∈ [x]) ∧
  (push 1)
    (assert (not (forall ((x A)) (contains x (mycons x mynil)))))
    (check-sat)
  (pop 1)
  ; (∀ x y, y ≠ x → x ∈ [y, y, x]) ∧
  (push 1)
    (assert (not
      (forall ((x A) (y A)) (=>
      (distinct x y)
      (contains x (mycons y (mycons y (mycons x mynil))))))))
    (check-sat)
  (pop 1)
  ; let (++)  = ‥ in
  (define-fun-rec append ((xs MyList) (ys MyList)) MyList
    (match xs (
      ((mycons x xs) (mycons x (append xs ys)))
      (mynil ys))))
  ; Hangs: (∀ x xs ys, x ∈ xs ++ ys <=> x ∈ xs ∨ x ∈ ys)
  (push 1)
    (assert (not
      (forall ((x A) (xs MyList) (ys MyList))
      (= (contains x (append xs ys)) (or (contains x xs) (contains x ys))))))
    ;(check-sat)
  (pop 1)
  ; Induction principle for lists
  (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
    (select f mynil)
    (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
    (select f xs))))
  ; Proof by induction:
  (push 1)
    ; Motive:
    (declare-const f (Array MyList Bool))
    (declare-const x A)
    (declare-const ys MyList)
    (assert (forall ((xs MyList))
      (= (select f xs)
        (= (contains x (append xs ys)) (or (contains x xs) (contains x ys))))))
    ; Base case is easy:
    (push 1) (assert (not (select f mynil))) (check-sat) (pop 1)
    ; So, to show (∀ xs, f[xs]), it suffices to show the inductive case
    ;   (∀ x xs, f[xs] → f[x ∷ xs])
    (push 1)
      (assert (forall ((x A) (xs MyList))
        (=> (select f xs) (select f (mycons x xs)))))
      (assert (not (forall ((xs MyList)) (select f xs))))
      (check-sat)
    (pop 1)
    ; To show the inductive case, first unfold (select f):
    (push 1)
      (assert (forall ((x A) (y A) (xs MyList) (ys MyList)) (=>
        (= (contains x (append xs ys)) (or (contains x xs) (contains x ys)))
        (= (contains x (append (mycons y xs) ys))
           (or (contains x (mycons y xs)) (contains x ys))))))
      (assert (not (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))))
      (check-sat)
    (pop 1)
    ; To show the inductive case, first unfold (select f) and simplify the call to (++):
    (push 1)
      (assert (forall ((x A) (y A) (xs MyList) (ys MyList)) (=>
        (= (contains x (append xs ys)) (or (contains x xs) (contains x ys)))
        (= (contains x (mycons y (append xs ys)))
           (or (contains x (mycons y xs)) (contains x ys))))))
      (assert (not (forall ((x A) (y A) (xs MyList) (ys MyList)) (=>
        (= (contains x (append xs ys)) (or (contains x xs) (contains x ys)))
        (= (contains x (append (mycons y xs) ys))
           (or (contains x (mycons y xs)) (contains x ys)))))))
      (check-sat)
    (pop 1)
    ; We would like to show that ∀ x y xs, x ∈ y ∷ xs <=> x = y ∨ x ∈ xs
    ; but solvers only see backward direction:
    (push 1)
      (assert (not
        (forall ((x A) (y A) (xs MyList))
        (=> (or (= x y) (contains x xs)) (contains x (mycons y xs))))))
      (check-sat)
    (pop 1)
    ; I guess this is because there is no way to invert the proof rules for (∈).
    ; Define one:
    ;   (∀ x xs,
    ;    x ∈ xs →
    ;    (∃ y ys, xs = y ∷ ys ∧ x = y) ∨
    ;    (∃ y ys, xs = y ∷ ys ∧ x ≠ y ∧ x ∈ ys))
    (assert (forall ((x A) (xs MyList)) (=> (contains x xs) (or
      (exists ((y A) (ys MyList)) (and (= xs (mycons y ys)) (= x y)))
      (exists ((y A) (ys MyList)) (and
        (= xs (mycons y ys))
        (distinct x y)
        (contains x ys)))))))
    ; Now can prove the lemma:
    (push 1)
      (assert (not
        (forall ((x A) (y A) (xs MyList))
        (= (or (= x y) (contains x xs)) (contains x (mycons y xs))))))
      (check-sat)
    (pop 1)
  (pop 1)
(pop 1)

; In fact, with this extra fact, solvers can prove the entire theorem on their own as long as the
; induction principle and motive are in scope. But, it takes a bit longer than usual
(push 1)
  (declare-sort A 0)
  (declare-datatype MyList ((mynil) (mycons (head A) (tail MyList))))
  ; Proof rules for (∈)
  (declare-fun contains (A MyList) Bool)
  (assert (forall ((x A)) (not (contains x mynil))))
  (assert (forall ((x A) (xs MyList)) (contains x (mycons x xs))))
  (assert (forall ((x A) (y A) (xs MyList)) (=>
    (distinct x y)
    (contains x xs)
    (contains x (mycons y xs)))))
  ; Inversion
  (assert (forall ((x A) (xs MyList)) (=> (contains x xs) (or
    (exists ((y A) (ys MyList)) (and (= xs (mycons y ys)) (= x y)))
    (exists ((y A) (ys MyList)) (and
      (= xs (mycons y ys))
      (distinct x y)
      (contains x ys)))))))
  ; let (++)  = ‥ in
  (define-fun-rec append ((xs MyList) (ys MyList)) MyList
    (match xs (
      ((mycons x xs) (mycons x (append xs ys)))
      (mynil ys))))
  ; Induction principle
  (assert (forall ((f (Array MyList Bool)) (xs MyList)) (=>
    (select f mynil)
    (forall ((x A) (xs MyList)) (=> (select f xs) (select f (mycons x xs))))
    (select f xs))))
  ; Motive
  (declare-const f (Array MyList Bool))
  (declare-const x A)
  (declare-const ys MyList)
  ; Proof
  (assert (forall ((xs MyList))
    (= (select f xs)
      (= (contains x (append xs ys)) (or (contains x xs) (contains x ys))))))
  (assert (not (forall ((xs MyList)) (select f xs))))
  (check-sat)
(pop 1)
