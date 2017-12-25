(***********************************************************)
(***********************************************************)
(****                                                   ****)
(****   Semantics of the simply-typed lambda calculus   ****)
(****                                                   ****)
(***********************************************************)
(***********************************************************)

Require Import Main.Stlc.Syntax.

Inductive value : term -> Prop :=
| vUnit : value eUnit
| vAbs : forall e x t, value (eAbs x t e).

Hint Constructors value.

Inductive step : term -> term -> Prop :=
| sBeta :
  forall e1 e2 x t,
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
