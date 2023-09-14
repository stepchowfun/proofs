(*********************)
(*********************)
(****             ****)
(****   Objects   ****)
(****             ****)
(*********************)
(*********************)

Require Import Coq.Classes.Morphisms.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

#[local] Set Universe Polymorphism.

Definition isomorphic {C} (x y : object C) :=
  exists (f : arrow x y), isomorphism f.

Definition uniqueUpToIsomorphism {C} (P : object C -> Prop) :=
  forall x y, P x -> P y -> isomorphic x y.

Theorem isomorphicRefl {C} (x : object C) : isomorphic x x.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  eSearch.
Qed.

#[export] Hint Resolve isomorphicRefl : main.

Theorem isomorphicTrans {C} (x y z : object C) :
  isomorphic x y -> isomorphic y z -> isomorphic x z.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  clean.
  exists (compose x2 x0).
  exists (compose x1 x3).
  split.
  - rewrite cAssoc.
    rewrite <- (cAssoc x0).
    rewrite H0.
    search.
  - rewrite cAssoc.
    rewrite <- (cAssoc x3).
    rewrite H2.
    search.
Qed.

(*
  We deliberately avoid adding a resolve hint for `isomorphicTrans` because
  doing so could lead to nonterminating searches.
*)

Theorem isomorphicSymm {C} (x y : object C) :
  isomorphic x y <-> isomorphic y x.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  eSearch.
Qed.

(*
  We deliberately avoid adding a resolve hint for `isomorphicSymm` because
  doing so could lead to nonterminating searches.
*)

Theorem opIsomorphic {C} x y :
  @isomorphic C x y <-> @isomorphic (oppositeCategory C) y x.
Proof.
  unfold isomorphic.
  split; clean; exists x0; [
    rewrite <- opIsomorphism | rewrite opIsomorphism
  ]; search.
Qed.

#[export] Hint Resolve opIsomorphic : main.
