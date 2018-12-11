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
  - rewrite cAssoc.
    rewrite <- (cAssoc C y x y z).
    rewrite H.
    magic.
  - rewrite cAssoc.
    rewrite <- (cAssoc C y z y x).
    rewrite H1.
    magic.
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
