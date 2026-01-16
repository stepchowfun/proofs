(***********************************)
(***********************************)
(****                           ****)
(****   The soundness theorem   ****)
(****                           ****)
(***********************************)
(***********************************)

Require Import main.system_f.context.
Require Import main.system_f.preservation.
Require Import main.system_f.progress.
Require Import main.system_f.semantics.
Require Import main.system_f.typing.
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
