(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Main.STLC.Semantics.
Require Import Main.STLC.Substitution.
Require Import Main.STLC.Syntax.
Require Import Main.STLC.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  intros. remember cEmpty. induction H; subst c; magic.
  - right. destruct IHhasType1; magic; destruct H2; eMagic.
  - right. destruct IHhasType1; destruct IHhasType2; eMagic.
    invert H; invert H1; eMagic.
Qed.

Hint Resolve progress.
