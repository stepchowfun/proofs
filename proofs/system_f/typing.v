(**************************)
(**************************)
(****                  ****)
(****   Typing rules   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import main.system_f.context.
Require Import main.system_f.free_var.
Require Import main.system_f.local_closure.
Require Import main.system_f.name.
Require Import main.system_f.opening.
Require Import main.system_f.syntax.
Require Import main.tactics.

Inductive HasType : Context -> Term -> Ty -> Prop :=
| ht_free_var :
  forall c t x,
  CWellFormed c ->
  e_lookup c x = Some t ->
  HasType c (e_free_var x) t
| ht_abs :
  forall c e l t1 t2,
  (
    forall x,
    ~ In x l ->
    HasType (c_e_extend c x t2) (ee_open e 0 (e_free_var x)) t1
  ) ->
  HasType c (e_abs t2 e) (t_arrow t2 t1)
| ht_app :
  forall c e1 e2 t1 t2,
  HasType c e1 (t_arrow t2 t1) ->
  HasType c e2 t2 ->
  HasType c (e_app e1 e2) t1
| ht_t_abs :
  forall c e l t,
  (
    forall x,
    ~ In x l ->
    HasType
      (c_t_extend c x)
      (et_open e 0 (t_free_var x))
      (tt_open t 0 (t_free_var x))
  ) ->
  HasType c (e_t_abs e) (t_for_all t)
| ht_t_app :
  forall c e t1 t2,
  TWellFormed c t2 ->
  HasType c e (t_for_all t1) ->
  HasType c (e_t_app e t2) (tt_open t1 0 t2).

Hint Constructors HasType : main.

(*****************************************)
(* The regularity of the typing judgment *)
(*****************************************)

Theorem typing_regularity :
  forall c e t,
  HasType c e t ->
  CWellFormed c /\ TWellFormed c t /\ ELocallyClosed e 0 0.
Proof.
  clean. induction H; clean.
  - split; search. split; search. unfold TWellFormed.
    split; induction H; search; unfold TWellFormed in H1; search; clean.
    destruct (name_eq x x0); search. invert H0. search.
  - pose proof (name_fresh l). clean. specialize (H0 x H1). clean. split.
    + invert H0. search.
    + split.
      * constructor; clean.
        -- constructor.
           ++ invert H0. unfold TWellFormed in H8. search.
           ++ unfold TWellFormed in H2. search.
        -- invert H0.
           unfold TWellFormed in H8.
           unfold TWellFormed in H2.
           search.
      * constructor.
        -- invert H0. unfold TWellFormed in H8. search.
        -- apply e_e_locally_closed_open with (e2 := e_free_var x). search.
  - split; search. split; search.
    unfold TWellFormed in H5. clean. invert H5. constructor; esearch.
  - pose proof (name_fresh (l ++ t_free_vars t)). clean.
    specialize (H0 x). feed H0. clean. split.
    + invert H0. search.
    + split.
      * constructor; clean.
        -- constructor. invert H2.
           apply t_t_locally_closed_open with (t2 := t_free_var x). search.
        -- invert H2. clean. unfold incl in *. clean.
           specialize (H5 a). feed H5. apply ttt_free_open. search.
      * constructor. apply e_t_locally_closed_open with (t := t_free_var x).
        search.
  - split; search. unfold TWellFormed in H. clean. split; search.
    constructor.
    + unfold TWellFormed in H2. apply locally_closed_open_for_all; search.
    + apply incl_tran with (m := t_free_vars t2 ++ t_free_vars t1).
      * apply ttt_free_open.
      * unfold TWellFormed in H2. search.
Qed.

Hint Resolve typing_regularity : main.

(*********************)
(* Context weakening *)
(*********************)

Theorem context_weakening :
  forall c1 c2 c3 e t,
  HasType (c_concat c1 c3) e t ->
  CWellFormed (c_concat (c_concat c1 c2) c3) ->
  HasType (c_concat (c_concat c1 c2) c3) e t.
Proof.
  clean. remember (c_concat c1 c3). outro c3. induction H; esearch; clean.
  - rewrite c_concat_assoc in *. constructor; search.
    pose proof (c_concat_e_lookup c1 c3 t x H0). esearch.
  - apply ht_abs with (l := l ++ e_domain c3 ++ e_domain c2 ++ e_domain c1).
    clean.
    specialize (H0 x). clean.
    specialize (H0 (c_e_extend c3 x t2)). clean.
    apply H0.
    constructor; search.
    + do 2 rewrite e_domain_concat. search.
    + pose proof (
        typing_regularity
        (c_e_extend (c_concat c1 c3) x t2)
        (ee_open e 0 (e_free_var x))
        t1
      ). clean.
      invert H3.
      unfold TWellFormed in *. clean. split; search.
      rewrite t_domain_concat in H6.
      do 2 rewrite t_domain_concat.
      unfold incl in *. clean.
      specialize (H6 a). clean.
      assert (In a (t_domain c3) \/ In a (t_domain c1)); search.
  - apply ht_t_abs with (l := l ++ t_domain c3 ++ t_domain c2 ++ t_domain c1).
    clean.
    specialize (H0 x). clean.
    specialize (H0 (c_t_extend c3 x)). clean.
    apply H0.
    constructor; search.
    do 2 rewrite t_domain_concat. search.
  - constructor; search.
    pose proof (typing_regularity (c_concat c1 c3) e (t_for_all t1)). clean.
    unfold TWellFormed in H. clean.
    constructor; search.
    rewrite t_domain_concat in H5.
    do 2 rewrite t_domain_concat.
    unfold incl in *. clean.
    specialize (H5 a). clean.
    assert (In a (t_domain c3) \/ In a (t_domain c1)); search.
Qed.

Hint Resolve context_weakening : main.
