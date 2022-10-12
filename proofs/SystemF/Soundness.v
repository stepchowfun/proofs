(***********************************)
(***********************************)
(****                           ****)
(****   The soundness theorem   ****)
(****                           ****)
(***********************************)
(***********************************)

Require Import Main.SystemF.Context.
Require Import Main.SystemF.Preservation.
Require Import Main.SystemF.Progress.
Require Import Main.SystemF.Semantics.
Require Import Main.SystemF.Typing.
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
