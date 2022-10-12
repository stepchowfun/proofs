(*****************************)
(*****************************)
(****                     ****)
(****   Initial objects   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Object.
Require Import Main.Tactics.

#[local] Set Universe Polymorphism.

Definition initial {C} (x : object C) :=
  forall y, exists f, forall (g : arrow x y), f = g.

Theorem initialUnique C : uniqueUpToIsomorphism (@initial C).
Proof.
  unfold uniqueUpToIsomorphism.
  unfold initial.
  unfold isomorphic.
  unfold isomorphism.
  clean.
  pose proof (H x). specialize (H y).
  pose proof (H0 x). specialize (H0 y).
  clean.
  exists x3.
  exists x0.
  split; search.
Qed.

#[export] Hint Resolve initialUnique : main.
