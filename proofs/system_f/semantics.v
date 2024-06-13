(***********************)
(***********************)
(****               ****)
(****   Semantics   ****)
(****               ****)
(***********************)
(***********************)

Require Import main.system_f.local_closure.
Require Import main.system_f.opening.
Require Import main.system_f.syntax.
Require Import main.tactics.

Inductive Value : Term -> Prop :=
| v_abs :
  forall e t,
  ELocallyClosed (e_abs t e) 0 0 ->
  Value (e_abs t e)
| v_t_abs :
  forall e,
  ELocallyClosed (e_t_abs e) 0 0 ->
  Value (e_t_abs e).

Hint Constructors Value : main.

Inductive Step : Term -> Term -> Prop :=
| s_beta :
  forall e1 e2 t,
  ELocallyClosed (e_abs t e1) 0 0 ->
  Value e2 ->
  Step (e_app (e_abs t e1) e2) (ee_open e1 0 e2)
| s_app1 :
  forall e1 e2 e3,
  ELocallyClosed e3 0 0 ->
  Step e1 e2 ->
  Step (e_app e1 e3) (e_app e2 e3)
| s_app2 :
  forall e1 e2 e3,
  Value e1 ->
  Step e2 e3 ->
  Step (e_app e1 e2) (e_app e1 e3)
| s_t_app :
  forall e1 e2 t,
  TLocallyClosed t 0 ->
  Step e1 e2 ->
  Step (e_t_app e1 t) (e_t_app e2 t)
| s_t_beta :
  forall e1 t,
  ELocallyClosed (e_t_abs e1) 0 0 ->
  TLocallyClosed t 0 ->
  Step (e_t_app (e_t_abs e1) t) (et_open e1 0 t).

Hint Constructors Step : main.

Theorem StepRegularity :
  forall e1 e2,
  Step e1 e2 ->
  ELocallyClosed e1 0 0 /\ ELocallyClosed e2 0 0.
Proof.
  clean. induction H; split; search; clean.
  - invert H0; search.
  - apply locally_closed_open_abs with (t := t); search. invert H0; search.
  - invert H; search.
  - invert H; search.
Qed.

Hint Resolve StepRegularity : main.

Inductive StepStar : Term -> Term -> Prop :=
| ss_refl :
  forall e,
  ELocallyClosed e 0 0 ->
  StepStar e e
| ss_step :
  forall e1 e2 e3,
  Step e1 e2 ->
  StepStar e2 e3 ->
  StepStar e1 e3.

Hint Constructors StepStar : main.

Theorem StepStarRegularity :
  forall e1 e2,
  StepStar e1 e2 ->
  ELocallyClosed e1 0 0 /\ ELocallyClosed e2 0 0.
Proof.
  clean. induction H; search. pose proof (StepRegularity e1 e2). search.
Qed.

Hint Resolve StepStarRegularity : main.
