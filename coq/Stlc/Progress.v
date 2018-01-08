(***********************************************************************)
(***********************************************************************)
(****                                                               ****)
(****   The progress theorem for the simply-typed lambda calculus   ****)
(****                                                               ****)
(***********************************************************************)
(***********************************************************************)

Require Import Main.Stlc.Semantics.
Require Import Main.Stlc.Syntax.
Require Import Main.Stlc.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  remember cEmpty.
  intros.
  induction H; magic.
  - feed IHhasType1; magic; destruct IHhasType1.
    + inversion H2; inversion H; magic.
    + destruct H2; right; exists (eIf x e2 e3); magic.
  - rewrite Heqc in H; inversion H.
  - feed IHhasType1; magic; feed IHhasType2; magic.
    destruct IHhasType1; destruct IHhasType2.
    + inversion H2; magic; rewrite <- H3 in H0; inversion H0.
    + destruct H2; right; exists (eApp x e1); magic.
    + destruct H1; right; exists (eApp e2 x); magic.
    + destruct H1; destruct H2; right; exists (eApp x0 e1); magic.
Qed.

Hint Resolve progress.
