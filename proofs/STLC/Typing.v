(**************************)
(**************************)
(****                  ****)
(****   Typing rules   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Main.STLC.Name.
Require Import Main.STLC.Syntax.

Inductive context :=
| cEmpty : context
| cExtend : context -> name -> type -> context.

Fixpoint lookup c1 x1 :=
  match c1 with
  | cEmpty => None
  | cExtend c2 x2 t => if nameEq x1 x2 then Some t else lookup c2 x1
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
  forall c t x,
  lookup c x = Some t ->
  hasType c (eVar x) t
| htAbs :
  forall c e t1 t2 x,
  hasType (cExtend c x t2) e t1 ->
  hasType c (eAbs x t2 e) (tArrow t2 t1)
| htApp :
  forall c e1 e2 t1 t2,
  hasType c e1 (tArrow t2 t1) ->
  hasType c e2 t2 ->
  hasType c (eApp e1 e2) t1.

Hint Constructors hasType : core.
