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

Definition isomorphic {C : category} (x y : object C) :=
  exists (f : arrow C x y), isomorphism f.

Definition uniqueUpToIsomorphism {C : category} (P : object C -> Prop) :=
  forall x y, P x -> P y -> isomorphic x y.

Theorem isomorphicRefl C x : @isomorphic C x x.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  eMagic.
Qed.

Hint Resolve isomorphicRefl.

Theorem isomorphicTrans C x y z :
  @isomorphic C x y -> @isomorphic C y z -> @isomorphic C x z.
Proof.
  unfold isomorphic.
  unfold isomorphism.
  unfold inverse.
  clean.
  exists (compose C x0 x2).
  exists (compose C x3 x1).
  split.
  - replace (compose C (compose C x0 x2) (compose C x3 x1))
      with (compose C (compose C x0 (compose C x2 x3)) x1).
    + rewrite H. magic.
    + repeat rewrite cAssoc. magic.
  - replace (compose C (compose C x3 x1) (compose C x0 x2))
      with (compose C (compose C x3 (compose C x1 x0)) x2).
    + rewrite H1. magic.
    + repeat rewrite cAssoc. magic.
Qed.

(*
  We deliberately avoid adding a resolve hint for isomorphicTrans because doing
  so could lead to nonterminating searches.
*)

Theorem isomorphicSymm C x y : @isomorphic C x y <-> @isomorphic C y x.
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
