(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Main.STLC.Name.
Require Import Main.STLC.Syntax.

Import Name.

Inductive freeVar : term -> name -> Prop :=
| fIf1 :
  forall e1 e2 e3 x,
  freeVar e1 x ->
  freeVar (eIf e1 e2 e3) x
| fIf2 :
  forall e1 e2 e3 x,
  freeVar e2 x ->
  freeVar (eIf e1 e2 e3) x
| fIf3 :
  forall e1 e2 e3 x,
  freeVar e3 x ->
  freeVar (eIf e1 e2 e3) x
| fVar :
  forall x,
  freeVar (eVar x) x
| fAbs :
  forall e t x1 x2,
  freeVar e x1 ->
  x1 <> x2 ->
  freeVar (eAbs x2 t e) x1
| fApp :
  forall e1 e2 x,
  freeVar e1 x \/ freeVar e2 x ->
  freeVar (eApp e1 e2) x.

Hint Constructors freeVar.
