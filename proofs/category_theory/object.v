(*********************)
(*********************)
(****             ****)
(****   Objects   ****)
(****             ****)
(*********************)
(*********************)

Require Import Stdlib.Classes.Morphisms.
Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

Definition Isomorphic [C] (x y : Object C) :=
  exists (f : Arrow x y), Isomorphism f.

Definition UniqueUpToIsomorphism [C] (P : Object C -> Prop) :=
  forall x y, P x -> P y -> Isomorphic x y.

Theorem isomorphic_refl [C] (x : Object C) : Isomorphic x x.
Proof.
  unfold Isomorphic.
  unfold Isomorphism.
  unfold Inverse.
  esearch.
Qed.

Hint Resolve isomorphic_refl : main.

Theorem isomorphic_trans [C] (x y z : Object C) :
  Isomorphic x y -> Isomorphic y z -> Isomorphic x z.
Proof.
  unfold Isomorphic.
  unfold Isomorphism.
  unfold Inverse.
  clean.
  exists (compose x2 x0).
  exists (compose x1 x3).
  split.
  - rewrite c_assoc.
    rewrite <- (c_assoc x0).
    rewrite H0.
    search.
  - rewrite c_assoc.
    rewrite <- (c_assoc x3).
    rewrite H2.
    search.
Qed.

(*
  We deliberately avoid adding a resolve hint for `isomorphic_trans` because
  doing so could lead to nonterminating searches.
*)

Theorem isomorphic_symm [C] (x y : Object C) :
  Isomorphic x y <-> Isomorphic y x.
Proof.
  unfold Isomorphic.
  unfold Isomorphism.
  unfold Inverse.
  esearch.
Qed.

(*
  We deliberately avoid adding a resolve hint for `isomorphic_symm` because
  doing so could lead to nonterminating searches.
*)

Theorem op_isomorphic [C] x y :
  @Isomorphic C x y <-> @Isomorphic (opposite_category C) y x.
Proof.
  unfold Isomorphic.
  split; clean; exists x0; [
    rewrite <- op_isomorphism | rewrite op_isomorphism
  ]; search.
Qed.

Hint Resolve op_isomorphic : main.
