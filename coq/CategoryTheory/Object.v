(*********************)
(*********************)
(****             ****)
(****   Objects   ****)
(****             ****)
(*********************)
(*********************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

Set Universe Polymorphism.

Definition isomorphic {C} (x y : object C) :=
  exists (f : arrow x y), isomorphism f.

Definition uniqueUpToIsomorphism {C} (P : object C -> Prop) :=
  forall x y, P x -> P y -> isomorphic x y.

Theorem isomorphicRefl C (x : object C) : isomorphic x x.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  eMagic.
Qed.

Hint Resolve isomorphicRefl.

Theorem isomorphicTrans C (x y z : object C) :
  isomorphic x y -> isomorphic y z -> isomorphic x z.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  clean.
  exists (compose x0 x2).
  exists (compose x3 x1).
  split.
  - rewrite cAssoc.
    rewrite <- (cAssoc x3).
    rewrite H.
    magic.
  - rewrite cAssoc.
    rewrite <- (cAssoc x0).
    rewrite H1.
    magic.
Qed.

(*
  We deliberately avoid adding a resolve hint for isomorphicTrans because doing
  so could lead to nonterminating searches.
*)

Theorem isomorphicSymm C (x y : object C) : isomorphic x y <-> isomorphic y x.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  eMagic.
Qed.

(*
  We deliberately avoid adding a resolve hint for isomorphicSymm because doing
  so could lead to nonterminating searches.
*)

Theorem opIsomorphic C x y :
  @isomorphic C x y <-> @isomorphic (oppositeCategory C) y x.
Proof.
  unfold isomorphic.
  split; clean; exists x0; [
    rewrite <- opIsomorphism | rewrite opIsomorphism
  ]; magic.
Qed.

Hint Resolve opIsomorphic.
