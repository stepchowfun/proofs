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

Lemma contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookupVar c1 x = lookupVar c2 x) ->
  hasType c2 e t.
Proof.
  clean. gen c2. induction H; magic; clean.
  - apply htVar. rewrite <- H0; magic.
  - apply htAbs. apply IHhasType. magic.
  - eapply htApp; magic.
Qed.

Hint Resolve contextInvariance.

Theorem typingJudgmentClosed :
  forall c e x t1,
  hasType c e t1 ->
  freeVar e x ->
  exists t2, lookupVar c x = Some t2.
Proof.
  clean. induction H; invert H0; eMagic.
Qed.

Hint Resolve typingJudgmentClosed.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  clean. gen c t2. induction e2; clean; invert H; eMagic; clean.
  - destruct (nameEq x n); destruct (nameEq n x); magic.
    eapply contextInvariance with (c1 := cEmpty); magic.
    clean. fact (typingJudgmentClosed cEmpty e1 x0 t1). magic.
  - destruct (nameEq x n); apply htAbs.
    + apply contextInvariance with (c1 := cExtend (cExtend c n t1) n t); magic.
    + apply IHe2.
      apply contextInvariance with (c1 := cExtend (cExtend c x t1) n t); magic.
Qed.

Hint Resolve substitutionPreservesTyping.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  clean. gen e2. remember cEmpty. induction H; magic; clean.
  - invert H2; magic.
  - invert H1; eMagic.
    apply substitutionPreservesTyping with (t1 := t2); magic.
    invert H; magic.
Qed.

Hint Resolve preservation.
