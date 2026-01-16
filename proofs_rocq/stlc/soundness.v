(***********************************)
(***********************************)
(****                           ****)
(****   The soundness theorem   ****)
(****                           ****)
(***********************************)
(***********************************)

Require Import main.stlc.preservation.
Require Import main.stlc.progress.
Require Import main.stlc.semantics.
Require Import main.stlc.typing.
Require Import main.tactics.

Theorem soundness :
  forall e1 e2 t,
  HasType c_empty e1 t ->
  StepStar e1 e2 ->
  (Value e2 \/ exists e3, Step e2 e3).
Proof.
  clean. induction H0; esearch.
Qed.

Hint Resolve soundness : main.
