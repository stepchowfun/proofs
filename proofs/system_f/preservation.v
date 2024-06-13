(**************************************)
(**************************************)
(****                              ****)
(****   The preservation theorem   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import main.system_f.context.
Require Import main.system_f.free_var.
Require Import main.system_f.name.
Require Import main.system_f.opening_substitution.
Require Import main.system_f.semantics.
Require Import main.system_f.substitution.
Require Import main.system_f.syntax.
Require Import main.system_f.typing.
Require Import main.tactics.

Theorem e_substitution_preserves_typing :
  forall c1 c2 e1 e2 t1 t2 x,
  HasType (c_concat (c_e_extend c1 x t2) c2) e1 t1 ->
  HasType c1 e2 t2 ->
  HasType (c_concat c1 c2) (ee_sub e1 x e2) t1.
Proof.
  clean. remember (c_concat (c_e_extend c1 x t2) c2). outro c2.
  induction H; esearch; clean.
  - destruct (name_eq x x0); clean.
    + pose proof (c_e_lookup_none (c_e_extend c1 x0 t2) c2 t2 x0). clean.
      pose proof (c_e_lookup_concat_left (c_e_extend c1 x0 t2) c2 t2 x0).
      clean.
      assert (t = t2); search. clean. clear H3.
      replace (c_concat c1 c2) with (c_concat (c_concat c1 c2) c_empty);
        search.
      apply context_weakening; search. clean.
      apply c_well_formed_e_skip with (t := t2) (x := x0). search.
    + constructor.
      * apply c_well_formed_e_skip with (t := t2) (x := x). search.
      * clear H H0. induction c2; search.
  - apply ht_abs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      c_e_extend (c_concat c1 c2) x0 t0
    ) with (
      c_concat c1 (c_e_extend c2 x0 t0)
    ); search.
    pose proof (typing_regularity c1 e2 t2).
    replace (e_free_var x0) with (ee_sub (e_free_var x0) x e2); search.
    rewrite <- eeee_sub_open with (it := 0); search.
  - apply ht_t_abs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      c_t_extend (c_concat c1 c2) x0
    ) with (
      c_concat c1 (c_t_extend c2 x0)
    ); search.
    pose proof (typing_regularity c1 e2 t2).
    rewrite <- eeet_sub_open with (ie := 0); search.
  - apply ht_t_app; search.
    unfold TWellFormed in *. clean. split; search.
    unfold incl in *. clean. specialize (H2 a). clean.
    rewrite t_domain_concat in *. clean. search.
Qed.

Hint Resolve e_substitution_preserves_typing : main.

Theorem t_substitution_preserves_typing :
  forall c1 c2 e t1 t2 x,
  HasType (c_concat (c_t_extend c1 x) c2) e t1 ->
  TWellFormed c1 t2 ->
  HasType (c_concat c1 (c_sub c2 x t2)) (et_sub e x t2) (tt_sub t1 x t2).
Proof.
  clean. remember (c_concat (c_t_extend c1 x) c2). outro c2.
  induction H; esearch; clean.
  - constructor.
    + apply c_well_formed_t_skip; search.
    + clear H0. induction c2; invert H; search; clean.
      rewrite ttt_sub_bound; search.
      pose proof (t_well_formed_closed c1 t x).
      feed H. apply t_lookup_well_formed with (x := x0); search.
  - apply ht_abs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      c_e_extend (c_concat c1 (c_sub c2 x t2)) x0 (tt_sub t0 x t2)
    ) with (
      c_concat c1 (c_e_extend (c_sub c2 x t2) x0 (tt_sub t0 x t2))
    ); search.
    unfold TWellFormed in H0.
    replace (e_free_var x0) with (et_sub (e_free_var x0) x t2); search.
    rewrite <- etee_sub_open; search.
    replace (
      c_e_extend (c_sub c2 x t2) x0 (tt_sub t0 x t2)
    ) with (
      c_sub (c_e_extend c2 x0 t0) x t2
    ); search.
  - apply ht_t_abs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      c_t_extend (c_concat c1 (c_sub c2 x t2)) x0
    ) with (
      c_concat c1 (c_sub (c_t_extend c2 x0) x t2)
    ); search.
    unfold TWellFormed in H0.
    replace (t_free_var x0) with (tt_sub (t_free_var x0) x t2); search.
    rewrite <- etet_sub_open; search.
    rewrite <- tttt_sub_open; search.
  - unfold TWellFormed in H0.
    rewrite tttt_sub_open; search.
    apply ht_t_app; search.
    unfold TWellFormed in *. clean.
    split; search.
    apply incl_tran with (
      m := t_free_vars t2 ++ remove name_eq x (t_free_vars t0)
    ); search.
    unfold incl in *. clean.
    pose proof (
      in_app_or (t_free_vars t2) (remove name_eq x (t_free_vars t0)) a H4
    ).
    clear H4. destruct H5; search.
    rewrite t_domain_concat in *.
    pose proof (name_in_remove (t_free_vars t0) a x H4). clean. clear H4.
    specialize (H3 a). feed H3.
    rewrite c_sub_t_domain.
    pose proof (in_app_or (t_domain c2) (x :: t_domain c1) a H3).
    destruct H4; search.
Qed.

Hint Resolve t_substitution_preserves_typing : main.

Theorem preservation :
  forall e1 e2 t,
  HasType c_empty e1 t ->
  Step e1 e2 ->
  HasType c_empty e2 t.
Proof.
  clean. outro e2. remember c_empty. induction H; search; clean.
  - invert H; search; invert H1; esearch.
    pose proof (name_fresh (ee_free_vars e ++ l)). clean.
    specialize (H5 x). feed H5.
    rewrite ee_sub_intro with (x := x); search.
    replace c_empty with (c_concat c_empty c_empty); esearch.
  - invert H0; search; invert H1; search.
    pose proof (name_fresh (et_free_vars e0 ++ t_free_vars t1 ++ l)). clean.
    specialize (H5 x). feed H5.
    rewrite et_sub_intro with (x := x); search.
    rewrite tt_sub_intro with (x := x); search.
    replace c_empty with (c_concat c_empty (c_sub c_empty x t2)); esearch.
Qed.

Hint Resolve preservation : main.
