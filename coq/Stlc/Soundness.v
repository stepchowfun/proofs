(************************************************************************)
(************************************************************************)
(****                                                                ****)
(****   The soundness theorem for the simply-typed lambda calculus   ****)
(****                                                                ****)
(************************************************************************)
(************************************************************************)

Require Import Main.Stlc.Preservation.
Require Import Main.Stlc.Progress.
Require Import Main.Stlc.Semantics.
Require Import Main.Stlc.Syntax.
Require Import Main.Stlc.Typing.
Require Import Main.Tactics.

Theorem soundness :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  stepStar e1 e2 ->
  (value e2 \/ exists e3, step e2 e3).
Proof.
  intros. induction H0.
  - apply progress with (t := t). magic.
  - feed IHstepStar.
    + apply preservation with (e1 := e1); magic.
    + magic.
Qed.
