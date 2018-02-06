(********************************************************)
(********************************************************)
(****                                                ****)
(****   Syntax of the simply-typed lambda calculus   ****)
(****                                                ****)
(********************************************************)
(********************************************************)

Require Import Main.STLC.Name.

Import Name.

Inductive term : Set :=
| eTrue : term
| eFalse : term
| eIf : term -> term -> term -> term
| eVar : name -> term
| eAbs : name -> type -> term -> term
| eApp : term -> term -> term

with type : Set :=
| tBool : type
| tArrow : type -> type -> type.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | eTrue => e1
  | eFalse => e1
  | eIf e3 e4 e5 => eIf (sub e3 x1 e2) (sub e4 x1 e2) (sub e5 x1 e2)
  | eVar x2 => if nameEq x1 x2 then e2 else e1
  | eAbs x2 t e3 => if nameEq x1 x2 then e1 else eAbs x2 t (sub e3 x1 e2)
  | eApp e3 e4 => eApp (sub e3 x1 e2) (sub e4 x1 e2)
  end.

Inductive freeVar : term -> name -> Prop :=
| fIf :
  forall e1 e2 e3 x,
  freeVar e1 x \/ freeVar e2 x \/ freeVar e3 x ->
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
