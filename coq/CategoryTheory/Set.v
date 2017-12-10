(*********************************************)
(*********************************************)
(****                                     ****)
(****   A proof that Set is a Category.   ****)
(****                                     ****)
(*********************************************)
(*********************************************)

Require Import Main.CategoryTheory.Definitions.

(**********************)
(* Set is a Category. *)
(**********************)

Module SetCategory <: Category.
  Definition Object := Set.
  Definition Arrow (X : Object) (Y : Object) := X -> Y.
  Definition compose {X Y Z} (f : Arrow Y Z) (g : Arrow X Y) x := f (g x).
  Definition id {X : Object} := fun (x : X) => x.

  Theorem assoc :
    forall W X Y Z (f : Arrow W X) (g : Arrow X Y) (h : Arrow Y Z),
    compose h (compose g f) = compose (compose h g) f.
  Proof.
    auto.
  Qed.

  Theorem ident :
    forall X Y,
    (forall (f : Arrow X Y), compose f id = f) /\
    (forall (f : Arrow Y X), compose id f = f).
  Proof.
    auto.
  Qed.
End SetCategory.
