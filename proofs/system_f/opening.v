(******************************)
(******************************)
(****                      ****)
(****   Variable opening   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import main.system_f.free_var.
Require Import main.system_f.local_closure.
Require Import main.system_f.syntax.
Require Import main.tactics.

Import Coq.Arith.PeanoNat.Nat.

Fixpoint ee_open e1 i1 e2 :=
  match e1 with
  | e_free_var _ => e1
  | e_bound_var i2 => if eq_nat_dec i1 i2 then e2 else e1
  | e_abs t e3 => e_abs t (ee_open e3 (S i1) e2)
  | e_app e3 e4 => e_app (ee_open e3 i1 e2) (ee_open e4 i1 e2)
  | e_t_abs e3 => e_t_abs (ee_open e3 i1 e2)
  | e_t_app e3 t => e_t_app (ee_open e3 i1 e2) t
  end.

Fixpoint tt_open t1 i1 t2 :=
  match t1 with
  | t_free_var _ => t1
  | t_bound_var i2 => if eq_nat_dec i1 i2 then t2 else t1
  | t_arrow t3 t4 => t_arrow (tt_open t3 i1 t2) (tt_open t4 i1 t2)
  | t_for_all t3 => t_for_all (tt_open t3 (S i1) t2)
  end.

Fixpoint et_open e1 i1 t1 :=
  match e1 with
  | e_free_var _ => e1
  | e_bound_var _ => e1
  | e_abs t2 e2 => e_abs (tt_open t2 i1 t1) (et_open e2 i1 t1)
  | e_app e2 e3 => e_app (et_open e2 i1 t1) (et_open e3 i1 t1)
  | e_t_abs e2 => e_t_abs (et_open e2 (S i1) t1)
  | e_t_app e2 t2 => e_t_app (et_open e2 i1 t1) (tt_open t2 i1 t1)
  end.

(*****************************************************)
(* Opening a locally closed term/type has no effect. *)
(*****************************************************)

Theorem ttt_open_locally_closed :
  forall i t1 t2,
  TLocallyClosed t1 i ->
  tt_open t1 i t2 = t1.
Proof.
  clean. induction H; search.
Qed.

#[export] Hint Resolve ttt_open_locally_closed : main.

Theorem eee_open_locally_closed :
  forall e1 e2 ie it,
  ELocallyClosed e1 ie it ->
  ee_open e1 ie e2 = e1.
Proof.
  clean. induction H; search.
Qed.

#[export] Hint Resolve eee_open_locally_closed : main.

Theorem eet_open_locally_closed :
  forall e ie it t,
  ELocallyClosed e ie it ->
  et_open e it t = e.
Proof.
  clean. induction H; search.
Qed.

#[export] Hint Resolve eet_open_locally_closed : main.

(***************************************************************************)
(* If the opening of a term/type is locally closed at some level, then the *)
(* term/type is locally closed at the next level.                          *)
(***************************************************************************)

Theorem t_t_locally_closed_open :
  forall i t1 t2,
  TLocallyClosed (tt_open t1 i t2) i ->
  TLocallyClosed t1 (S i).
Proof.
  clean. outro t1 i.
  induction t1; search; clean.
  - destruct (eq_dec i n); search.
    apply t_local_closure_monotonic with (i1 := i); search.
  - invert H. search.
  - invert H. search.
Qed.

#[export] Hint Resolve t_t_locally_closed_open : main.

Theorem e_e_locally_closed_open :
  forall e1 e2 ie it,
  ELocallyClosed (ee_open e1 ie e2) ie it ->
  ELocallyClosed e1 (S ie) it.
Proof.
  clean. outro e1 ie it.
  induction e1; search; clean.
  - destruct (eq_dec ie n); search.
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := it); search.
  - invert H. search.
  - invert H. search.
  - invert H. search.
  - invert H. search.
Qed.

#[export] Hint Resolve e_e_locally_closed_open : main.

Theorem e_t_locally_closed_open :
  forall e ie it t,
  ELocallyClosed (et_open e it t) ie it ->
  ELocallyClosed e ie (S it).
Proof.
  clean. outro e ie it.
  induction e; search; clean.
  - apply e_local_closure_monotonic with (ie1 := ie) (it1 := it); search.
  - invert H. esearch.
  - invert H. search.
  - invert H. search.
  - invert H. esearch.
Qed.

#[export] Hint Resolve e_t_locally_closed_open : main.

(********************************)
(* Free variables of an opening *)
(********************************)

Theorem ttt_free_open :
  forall i t1 t2,
  incl (t_free_vars (tt_open t1 i t2)) (t_free_vars t2 ++ t_free_vars t1) /\
  incl (t_free_vars t1) (t_free_vars (tt_open t1 i t2)).
Proof.
  clean. split; outro i.
  - induction t1; search. clean. apply incl_app.
    + apply incl_tran with (m := t_free_vars t2 ++ t_free_vars t1_1); search.
    + apply incl_tran with (m := t_free_vars t2 ++ t_free_vars t1_2); search.
  - induction t1; search. unfold incl. search.
Qed.

#[export] Hint Resolve ttt_free_open : main.

Theorem eeee_free_open :
  forall e1 e2 i,
  incl (ee_free_vars (ee_open e1 i e2)) (ee_free_vars e2 ++ ee_free_vars e1) /\
  incl (ee_free_vars e1) (ee_free_vars (ee_open e1 i e2)).
Proof.
  clean. split; outro i.
  - induction e1; search. clean. apply incl_app.
    + apply incl_tran with (m := ee_free_vars e2 ++ ee_free_vars e1_1); search.
    + apply incl_tran with (m := ee_free_vars e2 ++ ee_free_vars e1_2); search.
  - induction e1; search. unfold incl. search.
Qed.

#[export] Hint Resolve eeee_free_open : main.

Theorem eeet_free_open :
  forall e i t,
  incl (ee_free_vars (et_open e i t)) (ee_free_vars e) /\
  incl (ee_free_vars e) (ee_free_vars (et_open e i t)).
Proof.
  clean. split; outro i; induction e; search.
Qed.

#[export] Hint Resolve eeet_free_open : main.

Theorem etee_free_open :
  forall e1 e2 i,
  incl (et_free_vars (ee_open e1 i e2)) (et_free_vars e2 ++ et_free_vars e1) /\
  incl (et_free_vars e1) (et_free_vars (ee_open e1 i e2)).
Proof.
  clean. split; outro i.
  - induction e1; search; clean.
    + specialize (IHe1 (S i)). apply incl_app; search.
      apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1); search.
    + specialize (IHe1_1 i). specialize (IHe1_2 i). apply incl_app; search.
      * apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1_1);
          search.
      * apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1_2);
          search.
    + specialize (IHe1 i). apply incl_app; search.
      apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1); search.
  - induction e1; search. unfold incl. search.
Qed.

#[export] Hint Resolve etee_free_open : main.

Theorem etet_free_open :
  forall e i t,
  incl (et_free_vars (et_open e i t)) (t_free_vars t ++ et_free_vars e) /\
  incl (et_free_vars e) (et_free_vars (et_open e i t)).
Proof.
  clean. split; outro i.
  - induction e; search; clean; apply incl_app.
    + apply incl_tran with (m := t_free_vars t0 ++ t_free_vars t1); search.
      apply ttt_free_open.
    + apply incl_tran with (m := t_free_vars t0 ++ et_free_vars e); search.
    + apply incl_tran with (m := t_free_vars t0 ++ et_free_vars e1); search.
    + apply incl_tran with (m := t_free_vars t0 ++ et_free_vars e2); search.
    + apply incl_tran with (m := t_free_vars t0 ++ et_free_vars e); search.
    + apply incl_tran with (m := t_free_vars t0 ++ t_free_vars t1); search.
      apply ttt_free_open.
  - induction e; search; clean;
      specialize (IHe i); apply incl_app; search;
      apply incl_tran with (m := t_free_vars (tt_open t1 i t0)); search;
      apply ttt_free_open.
Qed.

#[export] Hint Resolve etet_free_open : main.

(********************************************)
(* Opening binders preserves local closure. *)
(********************************************)

Theorem locally_closed_open_for_all :
  forall i t1 t2,
  TLocallyClosed (t_for_all t1) i ->
  TLocallyClosed t2 i ->
  TLocallyClosed (tt_open t1 i t2) i.
Proof.
  clean. invert H.
  remember (S i). assert (n <= S i); search. clear Heqn. outro t2 i.
  induction H2; search; clean.
  specialize (IHTLocallyClosed t2 (S i)).
  feed IHTLocallyClosed.
  - apply t_local_closure_monotonic with (i1 := i); search.
  - apply tlc_for_all.
    apply IHTLocallyClosed.
    search.
Qed.

#[export] Hint Resolve locally_closed_open_for_all : main.

Theorem locally_closed_open_abs :
  forall e1 e2 ie it t,
  ELocallyClosed (e_abs t e1) ie it ->
  ELocallyClosed e2 ie it ->
  ELocallyClosed (ee_open e1 ie e2) ie it.
Proof.
  clean. invert H. clear t0 H3.
  remember (S ie). assert (n <= S ie); search. clear Heqn. outro e2 ie.
  induction H6; search; clean.
  - constructor; search.
    specialize (IHELocallyClosed e2 (S ie)).
    apply IHELocallyClosed; search.
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := nt); search.
  - constructor.
    specialize (IHELocallyClosed e2 ie).
    apply IHELocallyClosed; search.
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := nt); search.
Qed.

#[export] Hint Resolve locally_closed_open_abs : main.

Theorem locally_closed_open_t_abs :
  forall e ie it t,
  ELocallyClosed (e_t_abs e) ie it ->
  TLocallyClosed t it ->
  ELocallyClosed (et_open e it t) ie it.
Proof.
  clean. invert H.
  remember (S it). assert (n <= S it); search. clear Heqn. outro t0 it.
  induction H2; search; constructor; search; clean.
  - apply locally_closed_open_for_all; search.
    constructor.
    apply t_local_closure_monotonic with (i1 := nt); search.
  - specialize (IHELocallyClosed t0 (S it)).
    feed IHELocallyClosed.
    + apply t_local_closure_monotonic with (i1 := it); search.
    + apply IHELocallyClosed.
      search.
  - apply locally_closed_open_for_all; search.
    constructor.
    apply t_local_closure_monotonic with (i1 := nt); search.
Qed.

#[export] Hint Resolve locally_closed_open_t_abs : main.
