(***********************)
(***********************)
(****               ****)
(****   Semantics   ****)
(****               ****)
(***********************)
(***********************)

Require Import main.stlc.substitution.
Require Import main.stlc.syntax.

Inductive Value : Term -> Prop :=
| v_true : Value e_true
| v_false : Value e_false
| v_abs : forall e x t, Value (e_abs x t e).

#[export] Hint Constructors Value : main.

Inductive Step : Term -> Term -> Prop :=
| s_if1 :
  forall e1 e2 e3 e4,
  Step e1 e4 ->
  Step (e_if e1 e2 e3) (e_if e4 e2 e3)
| s_if2 :
  forall e1 e2,
  Step (e_if e_true e1 e2) e1
| s_if3 :
  forall e1 e2,
  Step (e_if e_false e1 e2) e2
| s_beta :
  forall e1 e2 t x,
  Value e2 ->
  Step (e_app (e_abs x t e1) e2) (sub e1 x e2)
| s_app1 :
  forall e1 e2 e3,
  Step e1 e2 ->
  Step (e_app e1 e3) (e_app e2 e3)
| s_app2 :
  forall e1 e2 e3,
  Value e1 ->
  Step e2 e3 ->
  Step (e_app e1 e2) (e_app e1 e3).

#[export] Hint Constructors Step : main.

Inductive StepStar : Term -> Term -> Prop :=
| ss_refl :
  forall e,
  StepStar e e
| ss_step :
  forall e1 e2 e3,
  Step e1 e2 ->
  StepStar e2 e3 ->
  StepStar e1 e3.

#[export] Hint Constructors StepStar : main.
