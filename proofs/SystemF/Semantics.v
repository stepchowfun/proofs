(***********************)
(***********************)
(****               ****)
(****   Semantics   ****)
(****               ****)
(***********************)
(***********************)

Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Opening.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Inductive value : term -> Prop :=
| vAbs :
  forall e t,
  eLocallyClosed (eAbs t e) 0 0 ->
  value (eAbs t e)
| vTAbs :
  forall e,
  eLocallyClosed (eTAbs e) 0 0 ->
  value (eTAbs e).

#[export] Hint Constructors value : main.

Inductive step : term -> term -> Prop :=
| sBeta :
  forall e1 e2 t,
  eLocallyClosed (eAbs t e1) 0 0 ->
  value e2 ->
  step (eApp (eAbs t e1) e2) (eeOpen e1 0 e2)
| sApp1 :
  forall e1 e2 e3,
  eLocallyClosed e3 0 0 ->
  step e1 e2 ->
  step (eApp e1 e3) (eApp e2 e3)
| sApp2 :
  forall e1 e2 e3,
  value e1 ->
  step e2 e3 ->
  step (eApp e1 e2) (eApp e1 e3)
| sTApp :
  forall e1 e2 t,
  tLocallyClosed t 0 ->
  step e1 e2 ->
  step (eTApp e1 t) (eTApp e2 t)
| sTBeta :
  forall e1 t,
  eLocallyClosed (eTAbs e1) 0 0 ->
  tLocallyClosed t 0 ->
  step (eTApp (eTAbs e1) t) (etOpen e1 0 t).

#[export] Hint Constructors step : main.

Theorem stepRegularity :
  forall e1 e2,
  step e1 e2 ->
  eLocallyClosed e1 0 0 /\ eLocallyClosed e2 0 0.
Proof.
  clean. induction H; split; search; clean.
  - invert H0; search.
  - apply locallyClosedOpenAbs with (t := t); search. invert H0; search.
  - invert H; search.
  - invert H; search.
Qed.

#[export] Hint Resolve stepRegularity : main.

Inductive stepStar : term -> term -> Prop :=
| scRefl :
  forall e,
  eLocallyClosed e 0 0 ->
  stepStar e e
| scStep :
  forall e1 e2 e3,
  step e1 e2 ->
  stepStar e2 e3 ->
  stepStar e1 e3.

#[export] Hint Constructors stepStar : main.

Theorem stepStarRegularity :
  forall e1 e2,
  stepStar e1 e2 ->
  eLocallyClosed e1 0 0 /\ eLocallyClosed e2 0 0.
Proof.
  clean. induction H; search. pose proof (stepRegularity e1 e2). search.
Qed.

#[export] Hint Resolve stepStarRegularity : main.
