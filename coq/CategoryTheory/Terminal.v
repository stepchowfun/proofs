(******************************)
(******************************)
(****                      ****)
(****   Terminal objects   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Initial.
Require Import Main.CategoryTheory.Object.
Require Import Main.Tactics.

Set Universe Polymorphism.

Definition terminal {C} x :=
  forall y,
  exists f,
  forall (g : arrow C y x), f = g.

Theorem opInitialTerminal C x :
  @initial C x <-> @terminal (oppositeCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opInitialTerminal.

Theorem opTerminalInitial C x :
  @terminal C x <->
  @initial (oppositeCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opTerminalInitial.

Theorem terminalUnique C : uniqueUpToIsomorphism (@terminal C).
Proof.
  unfold uniqueUpToIsomorphism.
  clean.
  rewrite opTerminalInitial in *.
  rewrite opIsomorphic.
  apply initialUnique; magic.
Qed.

Hint Resolve terminalUnique.
