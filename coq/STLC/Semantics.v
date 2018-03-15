(***********************)
(***********************)
(****               ****)
(****   Semantics   ****)
(****               ****)
(***********************)
(***********************)

Require Import Main.STLC.Substitution.
Require Import Main.STLC.Syntax.

Inductive value : term -> Prop :=
| vTrue : value eTrue
| vFalse : value eFalse
| vAbs : forall e x t, value (eAbs x t e).

Hint Constructors value.

Inductive step : term -> term -> Prop :=
| sIf1 :
  forall e1 e2 e3 e4,
  step e1 e4 ->
  step (eIf e1 e2 e3) (eIf e4 e2 e3)
| sIf2 :
  forall e1 e2,
  step (eIf eTrue e1 e2) e1
| sIf3 :
  forall e1 e2,
  step (eIf eFalse e1 e2) e2
| sBeta :
  forall e1 e2 t x,
  value e2 ->
  step (eApp (eAbs x t e1) e2) (sub e1 x e2)
| sApp1 :
  forall e1 e2 e3,
  step e1 e2 ->
  step (eApp e1 e3) (eApp e2 e3)
| sApp2 :
  forall e1 e2 e3,
  value e1 ->
  step e2 e3 ->
  step (eApp e1 e2) (eApp e1 e3).

Hint Constructors step.

Inductive stepStar : term -> term -> Prop :=
| scRefl :
  forall e,
  stepStar e e
| scStep :
  forall e1 e2 e3,
  step e1 e2 ->
  stepStar e2 e3 ->
  stepStar e1 e3.

Hint Constructors stepStar.
