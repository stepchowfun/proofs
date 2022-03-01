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
  clean. remember cEmpty. fact (typingRegularity c e1 t H).
  induction H; magic; right; clean.
  - fact (typingRegularity cEmpty e2 t2 H1).
    fact (typingRegularity cEmpty e1 (tArrow t2 t1) H).
    clean.
    destruct IHhasType1; destruct IHhasType2; eMagic.
    invert H; eMagic.
  - fact (typingRegularity cEmpty e (tForAll t1) H1).
    clean.
    destruct IHhasType; clean.
    + invert H1; magic. exists (etOpen e0 0 t2). invert H. magic.
    + exists (eTApp x t2). invert H. magic.
Qed.

#[export] Hint Resolve progress : main.
