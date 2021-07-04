; Semgus (https://pages.cs.wisc.edu/~loris/papers/popl21.pdf)
; Given a grammar
;   b ∷= true | false
;   e ∷= ebool b | eand e e
; We wish to prove
;   ∀ bstep,
;   (∀ b, bstep (ebool b) b) →
;   (∀ e₁ e₂ b₁ b₂, bstep e₁ b₁ → bstep e₂ b₂ → bstep (eand e₁ e₂) (and b₁ b₂)) →
;   ∃ e, e satisfies some spec w.r.t. bstep
; To prove any ∀-statement with SMT, need to negate and check for unsat.
; Negation is
;   ∃ bstep,
;   (∀ b, bstep (ebool b) b) ∧
;   (∀ e₁ e₂ b₁ b₂, bstep e₁ b₁ → bstep e₂ b₂ → bstep (eand e₁ e₂) (and b₁ b₂)) ∧
;   (∀ e, ¬ e satisfies some spec w.r.t. bstep)
; which is a CHC problem
(set-option :produce-proofs true)
(declare-datatype Exp ((ebool (get-bool Bool)) (eand (get-and1 Exp) (get-and2 Exp))))
(declare-fun bstep (Exp Bool) Bool)
(assert (forall ((b Bool)) (bstep (ebool b) b)))
(assert (forall ((e1 Exp) (e2 Exp) (b1 Bool) (b2 Bool)) (=>
  (bstep e1 b1)
  (bstep e2 b2)
  (bstep (eand e1 e2) (and b1 b2))
)))
(assert (forall ((e Exp)) (not (and
  (bstep e true)
  (match e (
    ((eand e1 e2)
      (match e2 (
        ((eand e1 e2) true)
        (x false))))
    (x false)))))))
(check-sat)
(get-proof)
; First two let bindings of proof construct the term
;   (eand (eand (ebool true) (ebool true)) (eand (ebool true) (ebool true)))
