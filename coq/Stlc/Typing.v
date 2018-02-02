(**************************************************************)
(**************************************************************)
(****                                                      ****)
(****   Typing rules of the simply-typed lambda calculus   ****)
(****                                                      ****)
(**************************************************************)
(**************************************************************)

Require Import Main.Stlc.Name.
Require Import Main.Stlc.Syntax.

Inductive context :=
| cEmpty : context
| cExtend : context -> name -> type -> context.

Fixpoint lookupVar c1 x1 :=
  match c1 with
  | cEmpty => None
  | cExtend c2 x2 t =>
    if nameEq x1 x2 then Some t else lookupVar c2 x1
  end.

Inductive hasType : context -> term -> type -> Prop :=
| htTrue :
  forall c,
  hasType c eTrue tBool
| htFalse :
  forall c,
  hasType c eFalse tBool
| htIf :
  forall c e1 e2 e3 t,
  hasType c e1 tBool ->
  hasType c e2 t ->
  hasType c e3 t ->
  hasType c (eIf e1 e2 e3) t
| htVar :
  forall x t c,
  lookupVar c x = Some t ->
  hasType c (eVar x) t
| htAbs :
  forall e x t1 t2 c,
  hasType (cExtend c x t1) e t2 ->
  hasType c (eAbs x t1 e) (tArrow t1 t2)
| htApp :
  forall e1 e2 t1 t2 c,
  hasType c e1 t1 ->
  hasType c e2 (tArrow t1 t2) ->
  hasType c (eApp e2 e1) t2.

Hint Constructors hasType.
