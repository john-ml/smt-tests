(set-option :produce-proofs true)

(declare-datatype Prod (par (A B) ((pair (fst A) (snd B)))))

(define-sort Var () Int)
(declare-datatype Exp (
  (LVar (lvar-x Var))
  (LBool (lbool-b Bool))
  (And (and-e1 Exp) (and-e2 Exp))
  (Let (let-x Var) (let-e1 Exp) (let-e2 Exp))
))

(define-sort Val () Bool)
(define-sort Env () (List (Prod Var Val)))

(declare-fun bstep (Env Exp Val) Bool)
(declare-fun find (Env Var Val) Bool)

(assert (forall ((x Var) (v Val) (rho Env)) (find (insert (pair x v) rho) x v)))
(assert (forall ((rho Env) (x Var) (v Val) (y Var) (w Val)) (=>
  (find rho x v)
  (distinct x y)
  (find (insert (pair y w) rho) x v)
)))

; Lookups seem to work
;(assert (not
;  (find
;    (insert (pair 0 true) (insert (pair 1 true) (insert (pair 2 false) nil)))
;    2 false)))
;(check-sat)
;(get-proof)

(assert (forall ((rho Env) (x Var) (v Val)) (=>
  (find rho x v)
  (bstep rho (LVar x) v))))
(assert (forall ((rho Env) (b Val)) (bstep rho (LBool b) b)))
(assert (forall ((rho Env) (e1 Exp) (e2 Exp) (b1 Bool) (b2 Bool)) (=>
  (bstep rho e1 b1)
  (bstep rho e2 b2)
  (bstep rho (And e1 e2) (and b1 b2))
)))
(assert (forall ((rho Env) (x Var) (e1 Exp) (e2 Exp) (b1 Bool) (b2 Bool)) (=>
  (bstep rho e1 b1)
  (bstep (insert (pair x b1) rho) e2 b2)
  (bstep rho (Let x e1 e2) b2)
)))

; To prove something like
;   ∀ ρ b₁ b₂, ρ ⊢ And (LBool b₁) (LBool b₂) ⇓ (b₁ && b₂)
; You can't use the usual trick where you assert
;   ¬ ρ ⊢ And (LBool b₁) (LBool b₂) ⇓ (b₁ && b₂)
; with ρ, b₁, b₂ free and check for unsat.
; This is logically equivalent but leaves the CHC fragment because ρ, b₁, and b₂ aren't relations.
; So the solver hangs.
(push)
(declare-const b1 Bool)
(declare-const b2 Bool)
(assert (not (bstep nil (And (LBool b1) (LBool b2)) (and b1 b2))))
;(check-sat)
(pop)

