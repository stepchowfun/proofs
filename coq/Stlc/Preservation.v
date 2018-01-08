(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   The preservation theorem for the simply-typed lambda calculus   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

Require Import Main.Stlc.Semantics.
Require Import Main.Stlc.Syntax.
Require Import Main.Stlc.Typing.
Require Import Main.Tactics.

Lemma contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookupVar c1 x = lookupVar c2 x) ->
  hasType c2 e t.
Proof.
  intros. generalize dependent c2.
  induction H; magic; intros.
  - apply htVar; rewrite <- H0; magic.
  - apply htAbs; apply IHhasType; intros; cbn;
      destruct (String.string_dec x0 x); magic; apply H0; magic.
  - apply htApp with (t1 := t1); magic.
Qed.

Hint Resolve contextInvariance.

Theorem typingJudgmentClosed :
  forall c e x t1,
  hasType c e t1 ->
  freeVar e x ->
  exists t2, lookupVar c x = Some t2.
Proof.
  intros; induction H; inversion H0; magic.
  - exists t; magic.
  - feed IHhasType; magic; destruct IHhasType; cbn in H7;
      destruct (String.string_dec x x0); magic.
Qed.

Hint Resolve typingJudgmentClosed.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  intros; generalize dependent c; generalize dependent t2.
  induction e2; intros; try abstract (inversion H; magic).
  - destruct (String.string_dec x s).
    + rewrite <- e in *.
      inversion H.
      cbn in H3; cbn; destruct (String.string_dec x x); magic.
      inversion H3; rewrite H6 in *.
      apply contextInvariance with (c1 := cEmpty); magic.
      intros.
      fact (typingJudgmentClosed cEmpty e1 x1 t2); repeat (feed H7; magic).
      destruct H7; inversion H7.
    + cbn; inversion H; inversion H3; destruct (String.string_dec x s);
        destruct (String.string_dec s x); magic.
  - cbn; destruct (String.string_dec x s).
    + rewrite e in *.
      apply contextInvariance with (c1 := cExtend c s t1); magic; intros.
      inversion H1.
      cbn; destruct (String.string_dec x0 s); magic.
    + inversion H. clear H.
      assert (hasType (cExtend (cExtend c s t) x t1) e2 t3); magic.
      apply contextInvariance with (c1 := cExtend (cExtend c x t1) s t); magic.
      intros.
      cbn; destruct (String.string_dec x1 s);
        destruct (String.string_dec x1 x); magic.
Qed.

Hint Resolve substitutionPreservesTyping.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  remember cEmpty.
  intros; generalize dependent e2.
  induction H; intros; try abstract (inversion H0).
  inversion H1; magic.
  inversion H0; magic.
  apply substitutionPreservesTyping with (t1 := t1); magic.
Qed.

Hint Resolve preservation.
