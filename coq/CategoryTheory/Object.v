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

(* Objects *)

Definition isomorphic {C : category} (x y : object C) :=
  exists (f : arrow C x y), isomorphism f.

Definition uniqueUpToIsomorphism {C : category} (P : object C -> Prop) :=
  forall x y, P x -> P y -> isomorphic x y.

Definition initial {C} x :=
  forall y,
  exists f,
  forall (g : arrow C x y), f = g.

Definition terminal {C} x :=
  forall y,
  exists f,
  forall (g : arrow C y x), f = g.

Theorem opInitialTerminal :
  forall C x,
  @initial C x <->
  @terminal (oppositeCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opInitialTerminal.

Theorem opTerminalInitial :
  forall C x,
  @terminal C x <->
  @initial (oppositeCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opTerminalInitial.

Theorem initialUnique : forall C, uniqueUpToIsomorphism (@initial C).
Proof.
  unfold uniqueUpToIsomorphism.
  unfold initial.
  unfold isomorphic.
  unfold isomorphism.
  clean.
  fact (H x). specialize (H y).
  fact (H0 x). specialize (H0 y).
  clean.
  exists x3.
  exists x0.
  split; magic.
Qed.

Hint Resolve initialUnique.

Theorem terminalUnique : forall C, uniqueUpToIsomorphism (@terminal C).
Proof.
  unfold uniqueUpToIsomorphism.
  clean.
  rewrite opTerminalInitial in *.
  apply opIso.
  apply initialUnique; magic.
Qed.

Hint Resolve terminalUnique.
