(**************************************)
(**************************************)
(****                              ****)
(****   The preservation theorem   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import main.stlc.free_var.
Require Import main.stlc.name.
Require Import main.stlc.semantics.
Require Import main.stlc.substitution.
Require Import main.stlc.typing.
Require Import main.tactics.

Theorem typing_judgment_closed :
  forall c e x t1,
  HasType c e t1 ->
  Free_var e x ->
  exists t2, lookup c x = Some t2.
Proof.
  clean. induction H; invert H0; esearch.
Qed.

#[export] Hint Resolve typing_judgment_closed : main.

Theorem context_invariance :
  forall c1 c2 e t,
  HasType c1 e t ->
  (forall x, Free_var e x -> lookup c1 x = lookup c2 x) ->
  HasType c2 e t.
Proof.
  clean. outro c2. induction H; search; clean.
  - apply ht_var. rewrite <- H0; search.
  - apply ht_abs. apply IHHasType. search.
  - eapply ht_app; search.
Qed.

#[export] Hint Resolve context_invariance : main.

Theorem substitution_preserves_typing :
  forall c x e1 e2 t1 t2,
  HasType (c_extend c x t1) e2 t2 ->
  HasType c_empty e1 t1 ->
  HasType c (sub e2 x e1) t2.
Proof.
  clean. outro c t2. induction e2; clean; invert H; esearch; clean.
  - destruct (name_eq x n); destruct (name_eq n x); search.
    apply context_invariance with (c1 := c_empty); search.
    clean. pose proof (typing_judgment_closed c_empty e1 x0 t1). search.
  - destruct (name_eq x n); apply ht_abs.
    + apply context_invariance with (c1 := c_extend (c_extend c n t1) n t);
      search.
    + apply IHe2.
      apply context_invariance with (c1 := c_extend (c_extend c x t1) n t);
      search.
Qed.

#[export] Hint Resolve substitution_preserves_typing : main.

Theorem preservation :
  forall e1 e2 t,
  HasType c_empty e1 t ->
  Step e1 e2 ->
  HasType c_empty e2 t.
Proof.
  clean. outro e2. remember c_empty. induction H; search; clean.
  - invert H2; search.
  - invert H1; esearch.
    apply substitution_preserves_typing with (t1 := t2); search.
    invert H; search.
Qed.

#[export] Hint Resolve preservation : main.
