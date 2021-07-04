(set-option :produce-proofs true)
(define-sort Var () Int)
(declare-datatype Exp (
  (LVar (var-x Var))
  (Lit (lit-b Bool))
  (And (and-e1 Exp) (and-e2 Exp))
  (Let (let-x Var) (let-e1 Exp) (let-e2 Exp))
))
(define-sort Env () (Array Var Bool))
(declare-fun bstep (Env Exp Bool) Bool)
(assert (forall ((rho Env) (b Bool)) (bstep rho (Lit b) b)))
(assert (forall ((rho Env) (x Var)) (bstep rho (LVar x) (select rho x))))
(assert (forall ((rho Env) (e1 Exp) (e2 Exp) (b1 Bool) (b2 Bool)) (=>
  (bstep rho e1 b1)
  (bstep rho e2 b2)
  (bstep rho (And e1 e2) (and b1 b2))
)))
;(assert (forall ((rho Env) (x Var) (e1 Exp) (e2 Exp) (b1 Bool) (b2 Bool)) (=>
;  (bstep rho e1 b1)
;  (bstep (store rho x b1) e2 b2)
;  (bstep rho (Let x e1 e2) b2)
;)))
(assert (forall ((e Exp)) (not (and
  (bstep ((as const (Array Int Bool)) false) e true)))))
; Hangs
;(check-sat)
;(get-proof)
