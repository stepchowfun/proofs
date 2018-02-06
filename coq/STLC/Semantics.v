(***********************************************************)
(***********************************************************)
(****                                                   ****)
(****   Semantics of the simply-typed lambda calculus   ****)
(****                                                   ****)
(***********************************************************)
(***********************************************************)

Require Import Main.STLC.Name.
Require Import Main.STLC.Syntax.

Import Name.

Inductive value : term -> Prop :=
| vTrue : value eTrue
| vFalse : value eFalse
| vAbs : forall e x t, value (eAbs x t e).

Hint Constructors value.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | eTrue => e1
  | eFalse => e1
  | eIf e3 e4 e5 => eIf (sub e3 x1 e2) (sub e4 x1 e2) (sub e5 x1 e2)
  | eVar x2 => if nameEq x1 x2 then e2 else e1
  | eAbs x2 t e3 => if nameEq x1 x2 then e1 else eAbs x2 t (sub e3 x1 e2)
  | eApp e3 e4 => eApp (sub e3 x1 e2) (sub e4 x1 e2)
  end.

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
