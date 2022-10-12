(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Main.STLC.Semantics.
Require Import Main.STLC.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  clean. remember cEmpty. induction H; search; clean; right.
  - destruct IHhasType1; destruct H2; eSearch.
  - destruct IHhasType1; destruct IHhasType2; eSearch. invert H; eSearch.
Qed.

#[export] Hint Resolve progress : main.
