(********************************************************)
(********************************************************)
(****                                                ****)
(****   Syntax of the simply-typed lambda calculus   ****)
(****                                                ****)
(********************************************************)
(********************************************************)

Require Import Coq.Strings.String.

Inductive term : Set :=
| eUnit : term
| eVar : string -> term
| eAbs : string -> type -> term -> term
| eApp : term -> term -> term

with type : Set :=
| tUnit : type
| tArrow : type -> type -> type.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | eUnit => e1
  | eVar x2 => if string_dec x1 x2 then e2 else e1
  | eAbs x2 t e3 => if string_dec x1 x2 then e1 else eAbs x2 t (sub e3 x1 e2)
  | eApp e3 e4 => eApp (sub e3 x1 e2) (sub e4 x1 e2)
  end.

Inductive freeVar : term -> string -> Prop :=
| fVar :
  forall x,
  freeVar (eVar x) x
| fAbs :
  forall e x1 x2 t,
  freeVar e x1 ->
  x1 <> x2 ->
  freeVar (eAbs x2 t e) x1
| fApp :
  forall x e1 e2,
  freeVar e1 x \/ freeVar e2 x ->
  freeVar (eApp e1 e2) x.

Hint Constructors freeVar.
