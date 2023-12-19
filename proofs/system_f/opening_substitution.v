(**************************************************************************)
(**************************************************************************)
(****                                                                  ****)
(****   Facts about the interaction between opening and substitution   ****)
(****                                                                  ****)
(**************************************************************************)
(**************************************************************************)

Require Import Coq.Lists.List.
Require Import main.system_f.free_var.
Require Import main.system_f.local_closure.
Require Import main.system_f.name.
Require Import main.system_f.opening.
Require Import main.system_f.substitution.
Require Import main.system_f.syntax.
Require Import main.tactics.

(*****************************)
(* Substitution introduction *)
(*****************************)

Theorem tt_sub_intro :
  forall i t1 t2 x,
  ~ In x (t_free_vars t1) ->
  tt_open t1 i t2 = (tt_sub (tt_open t1 i (t_free_var x)) x t2).
Proof.
  clean. outro i. induction t1; search.
Qed.

#[export] Hint Resolve tt_sub_intro : main.

Theorem ee_sub_intro :
  forall e1 e2 i x,
  ~ In x (ee_free_vars e1) ->
  ee_open e1 i e2 = (ee_sub (ee_open e1 i (e_free_var x)) x e2).
Proof.
  induction e1; search.
Qed.

#[export] Hint Resolve ee_sub_intro : main.

Theorem et_sub_intro :
  forall e i t x,
  ~ In x (et_free_vars e) ->
  et_open e i t = (et_sub (et_open e i (t_free_var x)) x t).
Proof.
  induction e; search; clean; rewrite tt_sub_intro with (x := x); search.
Qed.

#[export] Hint Resolve et_sub_intro : main.

(******************************************)
(* Substitution distributes over opening. *)
(******************************************)

Theorem tttt_sub_open :
  forall i t1 t2 t3 x,
  TLocallyClosed t2 i ->
  tt_sub (tt_open t1 i t3) x t2 = tt_open (tt_sub t1 x t2) i (tt_sub t3 x t2).
Proof.
  clean. outro i. induction t1; search; clean.
  - destruct (name_eq x n); search. rewrite ttt_open_locally_closed; search.
  - specialize (IHt1 (S i)). feed IHt1.
    apply t_local_closure_monotonic with (i1 := i); search.
Qed.

#[export] Hint Resolve tttt_sub_open : main.

Theorem eeee_sub_open :
  forall e1 e2 e3 ie it x,
  ELocallyClosed e2 ie it ->
  ee_sub (ee_open e1 ie e3) x e2 =
    ee_open (ee_sub e1 x e2) ie (ee_sub e3 x e2).
Proof.
  clean. outro ie. induction e1; search; clean.
  - destruct (name_eq x n); search.
    rewrite eee_open_locally_closed with (it := it); search.
  - specialize (IHe1 (S ie)). feed IHe1.
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := it); search.
Qed.

#[export] Hint Resolve eeee_sub_open : main.

Theorem eeet_sub_open :
  forall e1 e2 ie it t x,
  ELocallyClosed e2 ie it ->
  ee_sub (et_open e1 it t) x e2 = et_open (ee_sub e1 x e2) it t.
Proof.
  clean. outro it. induction e1; search; clean.
  - destruct (name_eq x n); search.
    rewrite eet_open_locally_closed with (ie := ie) (it := it); search.
  - specialize (IHe1 (S it)). feed IHe1.
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := it); search.
Qed.

#[export] Hint Resolve eeet_sub_open : main.

Theorem etee_sub_open :
  forall i e1 e2 t x,
  TLocallyClosed t i ->
  et_sub (ee_open e1 i e2) x t = ee_open (et_sub e1 x t) i (et_sub e2 x t).
Proof.
  clean. outro i. induction e1; search; clean.
  specialize (IHe1 (S i)). feed IHe1.
  apply t_local_closure_monotonic with (i1 := i); search.
Qed.

#[export] Hint Resolve etee_sub_open : main.

Theorem etet_sub_open :
  forall i e t1 t2 x,
  TLocallyClosed t1 i ->
  et_sub (et_open e i t2) x t1 = et_open (et_sub e x t1) i (tt_sub t2 x t1).
Proof.
  clean. outro i. induction e; search; clean.
  specialize (IHe (S i)). feed IHe.
  apply t_local_closure_monotonic with (i1 := i); search.
Qed.

#[export] Hint Resolve etet_sub_open : main.
