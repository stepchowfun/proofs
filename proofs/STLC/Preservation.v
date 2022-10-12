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

Theorem typingJudgmentClosed :
  forall c e x t1,
  hasType c e t1 ->
  freeVar e x ->
  exists t2, lookup c x = Some t2.
Proof.
  clean. induction H; invert H0; eSearch.
Qed.

#[export] Hint Resolve typingJudgmentClosed : main.

Theorem contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookup c1 x = lookup c2 x) ->
  hasType c2 e t.
Proof.
  clean. outro c2. induction H; search; clean.
  - apply htVar. rewrite <- H0; search.
  - apply htAbs. apply IHhasType. search.
  - eapply htApp; search.
Qed.

#[export] Hint Resolve contextInvariance : main.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  clean. outro c t2. induction e2; clean; invert H; eSearch; clean.
  - destruct (nameEq x n); destruct (nameEq n x); search.
    apply contextInvariance with (c1 := cEmpty); search.
    clean. pose proof (typingJudgmentClosed cEmpty e1 x0 t1). search.
  - destruct (nameEq x n); apply htAbs.
    + apply contextInvariance with (c1 := cExtend (cExtend c n t1) n t);
      search.
    + apply IHe2.
      apply contextInvariance with (c1 := cExtend (cExtend c x t1) n t);
      search.
Qed.

#[export] Hint Resolve substitutionPreservesTyping : main.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  clean. outro e2. remember cEmpty. induction H; search; clean.
  - invert H2; search.
  - invert H1; eSearch.
    apply substitutionPreservesTyping with (t1 := t2); search.
    invert H; search.
Qed.

#[export] Hint Resolve preservation : main.
