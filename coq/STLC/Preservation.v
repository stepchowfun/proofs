(**************************************)
(**************************************)
(****                              ****)
(****   The preservation theorem   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Main.STLC.FreeVar.
Require Import Main.STLC.Name.
Require Import Main.STLC.Semantics.
Require Import Main.STLC.Substitution.
Require Import Main.STLC.Typing.
Require Import Main.Tactics.

Import Name.

Lemma contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookupVar c1 x = lookupVar c2 x) ->
  hasType c2 e t.
Proof.
  clean. generalize dependent c2.
  induction H; magic; clean.
  - apply htVar. rewrite <- H0; magic.
  - apply htAbs. apply IHhasType. clean. destruct (nameEq x0 x); magic.
  - apply htApp with (t2 := t2); magic.
Qed.

Hint Resolve contextInvariance.

Theorem typingJudgmentClosed :
  forall c e x t1,
  hasType c e t1 ->
  freeVar e x ->
  exists t2, lookupVar c x = Some t2.
Proof.
  clean. induction H; invert H0; eMagic.
  clean. destruct (nameEq x x0); eMagic.
Qed.

Hint Resolve typingJudgmentClosed.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  clean. generalize dependent c. generalize dependent t2.
  induction e2; clean; invert H; eMagic; clean.
  - destruct (nameEq x n); destruct (nameEq n x); magic.
    apply contextInvariance with (c1 := cEmpty); magic.
    clean.
    fact (typingJudgmentClosed cEmpty e1 x0 t1).
    repeat (feed H1).
  - destruct (nameEq x n); apply htAbs.
    + apply contextInvariance with (c1 := cExtend (cExtend c n t1) n t); magic.
      clean.
      destruct (nameEq x0 n); magic.
    + apply IHe2.
      apply contextInvariance with (c1 := cExtend (cExtend c x t1) n t); magic.
      clean.
      destruct (nameEq x0 n); destruct (nameEq x0 x); magic.
Qed.

Hint Resolve substitutionPreservesTyping.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  clean. generalize dependent e2.
  remember cEmpty. induction H; clean; try solve [invert H0].
  - invert H2; magic.
  - invert H1; eMagic.
    apply substitutionPreservesTyping with (t1 := t2); magic.
    invert H; magic.
Qed.

Hint Resolve preservation.
