(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   The preservation theorem for the simply-typed lambda calculus   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

Require Import Main.STLC.Name.
Require Import Main.STLC.Semantics.
Require Import Main.STLC.Syntax.
Require Import Main.STLC.Typing.
Require Import Main.Tactics.

Lemma contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookupVar c1 x = lookupVar c2 x) ->
  hasType c2 e t.
Proof.
  intros. generalize dependent c2.
  induction H; magic; intros.
  - apply htIf; apply IHhasType1 + apply IHhasType2 + apply IHhasType3;
      intros; apply H2; magic.
  - apply htVar. rewrite <- H0; magic.
  - apply htAbs. apply IHhasType. intros. cbn.
    destruct (nameEq x0 x); magic. apply H0. magic.
  - apply htApp with (t2 := t2); magic.
Qed.

Hint Resolve contextInvariance.

Theorem typingJudgmentClosed :
  forall c e x t1,
  hasType c e t1 ->
  freeVar e x ->
  exists t2, lookupVar c x = Some t2.
Proof.
  intros. induction H; invert H0; magic.
  - exists t. magic.
  - feed IHhasType; magic.
    destruct IHhasType. cbn in H0.
    destruct (nameEq x x0); magic.
    exists x1. magic.
Qed.

Hint Resolve typingJudgmentClosed.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  intros. generalize dependent c. generalize dependent t2.
  induction e2; intros; invert H; magic.
  - cbn. cbn in H3.
    destruct (nameEq x n); destruct (nameEq n x); magic.
    apply contextInvariance with (c1 := cEmpty); magic.
    intros.
    fact (typingJudgmentClosed cEmpty e1 x0 t1).
    do 2 (feed H1; magic).
    destruct H1. invert H1.
  - cbn.
    destruct (nameEq x n); apply htAbs.
    + apply contextInvariance with (c1 := cExtend (cExtend c n t1) n t); magic.
      intros. cbn.
      destruct (nameEq x0 n); magic.
    + apply IHe2.
      apply contextInvariance with (c1 := cExtend (cExtend c x t1) n t); magic.
      intros. cbn.
      destruct (nameEq x0 n); destruct (nameEq x0 x); magic.
  - cbn. apply htApp with (t2 := t3); magic.
Qed.

Hint Resolve substitutionPreservesTyping.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  intros. generalize dependent e2.
  remember cEmpty. induction H; subst c; intros; try abstract (invert H0).
  - invert H2; magic.
  - invert H1; magic.
    + apply substitutionPreservesTyping with (t1 := t2); magic.
      invert H; magic.
    + apply htApp with (t2 := t2); magic.
    + apply htApp with (t2 := t2); magic.
Qed.

Hint Resolve preservation.
