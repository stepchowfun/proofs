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
  - right. destruct IHhasType1; magic; destruct H2; magic.
    + exists e2. magic.
    + exists e3. magic.
    + exists (eIf x e2 e3). magic.
  - right. destruct IHhasType1; destruct IHhasType2; magic.
    + invert H; invert H1; magic. exists (sub e x e2). magic.
    + destruct H2. exists (eApp e1 x). magic.
    + destruct H1. exists (eApp x e2). magic.
    + destruct H1. exists (eApp x e2). magic.
Qed.

Hint Resolve progress.
