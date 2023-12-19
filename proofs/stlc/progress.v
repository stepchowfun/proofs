(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import main.stlc.semantics.
Require Import main.stlc.typing.
Require Import main.tactics.

Theorem progress :
  forall e1 t,
  HasType c_empty e1 t ->
  Value e1 \/ exists e2, Step e1 e2.
Proof.
  clean. remember c_empty. induction H; search; clean; right.
  - destruct IHHasType1; destruct H2; esearch.
  - destruct IHHasType1; destruct IHHasType2; esearch. invert H; esearch.
Qed.

#[export] Hint Resolve progress : main.
