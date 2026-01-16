(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Stdlib.Logic.ProofIrrelevance.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

(* Metavariables for categories: `C`, `D`, `E` *)

Record IsCategory
  (Object : Type) (* Objects: `w`, `x`, `y`, `z` *)
  (Arrow : Object -> Object -> Type) (* Arrows: `f`, `g`, `h` *)
  (id : forall x, Arrow x x)
  (compose : forall [x y z], Arrow x y -> Arrow y z -> Arrow x z)
:= {
  is_c_ident_left x y (f : Arrow x y) : compose (id x) f = f;
  is_c_ident_right x y (f : Arrow x y) : compose f (id y) = f;
  is_c_assoc w x y z (f : Arrow w x) (g : Arrow x y) (h : Arrow y z) :
    compose (compose f g) h = compose f (compose g h);
}.

Arguments is_c_ident_left [_ _ _ _ _ _ _] _.
Arguments is_c_ident_right [_ _ _ _ _ _ _] _.
Arguments is_c_assoc [_ _ _ _ _ _ _ _ _] _ _ _.

Hint Constructors IsCategory : main.

Record Category := {
  Object; Arrow; id; compose;
  category_laws : IsCategory Object Arrow id compose;
}.

Arguments Arrow [_] _ _.
Arguments id [_] _.
Arguments compose [_ _ _ _] _ _.

Definition c_ident_left [C : Category] [x y : Object C] (f : Arrow x y) :
  compose (id x) f = f
:= C.(category_laws).(is_c_ident_left) f.

Definition c_ident_right [C : Category] [x y : Object C] (f : Arrow x y) :
  compose f (id y) = f
:= C.(category_laws).(is_c_ident_right) f.

Definition c_assoc
  [C : Category]
  [w x y z : Object C]
  (f : Arrow w x)
  (g : Arrow x y)
  (h : Arrow y z) :
  compose (compose f g) h = compose f (compose g h)
:= C.(category_laws).(is_c_assoc) f g h.

Hint Resolve c_assoc : main.
Hint Resolve c_ident_left : main.
Hint Rewrite @c_ident_left : main.
Hint Resolve c_ident_right : main.
Hint Rewrite @c_ident_right : main.

#[program] Definition opposite_category C : Category := {|
  Object := Object C;
  Arrow f g := Arrow g f;
  id x := id x;
  compose _ _ _ f g := compose g f;
|}.

Theorem opposite_involution C : opposite_category (opposite_category C) = C.
Proof.
  destruct C.
  unfold opposite_category.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve opposite_involution : main.
