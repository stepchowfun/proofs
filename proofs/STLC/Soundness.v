(***********************************)
(***********************************)
(****                           ****)
(****   The soundness theorem   ****)
(****                           ****)
(***********************************)
(***********************************)

Require Import Main.STLC.Preservation.
Require Import Main.STLC.Progress.
Require Import Main.STLC.Semantics.
Require Import Main.STLC.Typing.
Require Import Main.Tactics.

Theorem soundness :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  stepStar e1 e2 ->
  (value e2 \/ exists e3, step e2 e3).
Proof.
  clean. induction H0; eSearch.
Qed.

#[export] Hint Resolve soundness : main.
