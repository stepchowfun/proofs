(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Main.SystemF.Context.
Require Import Main.SystemF.Opening.
Require Import Main.SystemF.Semantics.
Require Import Main.SystemF.Syntax.
Require Import Main.SystemF.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  clean. remember cEmpty. pose proof (typingRegularity c e1 t H).
  induction H; search; right; clean.
  - pose proof (typingRegularity cEmpty e2 t2 H1).
    pose proof (typingRegularity cEmpty e1 (tArrow t2 t1) H).
    clean.
    destruct IHhasType1; destruct IHhasType2; eSearch.
    invert H; eSearch.
  - pose proof (typingRegularity cEmpty e (tForAll t1) H1).
    clean.
    destruct IHhasType; clean.
    + invert H1; search. exists (etOpen e0 0 t2). invert H. search.
    + exists (eTApp x t2). invert H. search.
Qed.

#[export] Hint Resolve progress : main.
