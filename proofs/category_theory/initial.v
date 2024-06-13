(*****************************)
(*****************************)
(****                     ****)
(****   Initial objects   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.category_theory.object.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

Definition initial [C] (x : Object C) :=
  forall y, exists f, forall (g : Arrow x y), f = g.

Theorem initial_unique C : UniqueUpToIsomorphism (@initial C).
Proof.
  unfold UniqueUpToIsomorphism.
  unfold initial.
  unfold Isomorphic.
  unfold Isomorphism.
  clean.
  pose proof (H x). specialize (H y).
  pose proof (H0 x). specialize (H0 y).
  clean.
  exists x3.
  exists x0.
  split; search.
Qed.

Hint Resolve initial_unique : main.
