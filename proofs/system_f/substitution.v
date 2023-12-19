(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Lists.List.
Require Import main.system_f.free_var.
Require Import main.system_f.local_closure.
Require Import main.system_f.name.
Require Import main.system_f.syntax.
Require Import main.tactics.

Fixpoint ee_sub e1 x1 e2 :=
  match e1 with
  | e_free_var x2 => if name_eq x1 x2 then e2 else e1
  | e_bound_var _ => e1
  | e_abs t e3 => e_abs t (ee_sub e3 x1 e2)
  | e_app e3 e4 => e_app (ee_sub e3 x1 e2) (ee_sub e4 x1 e2)
  | e_t_abs e3 => e_t_abs (ee_sub e3 x1 e2)
  | e_t_app e3 t => e_t_app (ee_sub e3 x1 e2) t
  end.

Fixpoint tt_sub t1 x1 t2 :=
  match t1 with
  | t_free_var x2 => if name_eq x1 x2 then t2 else t1
  | t_bound_var _ => t1
  | t_arrow t3 t4 => t_arrow (tt_sub t3 x1 t2) (tt_sub t4 x1 t2)
  | t_for_all t3 => t_for_all (tt_sub t3 x1 t2)
  end.

Fixpoint et_sub e1 x1 t1 :=
  match e1 with
  | e_free_var _ => e1
  | e_bound_var _ => e1
  | e_abs t2 e2 => e_abs (tt_sub t2 x1 t1) (et_sub e2 x1 t1)
  | e_app e2 e3 => e_app (et_sub e2 x1 t1) (et_sub e3 x1 t1)
  | e_t_abs e2 => e_t_abs (et_sub e2 x1 t1)
  | e_t_app e2 t2 => e_t_app (et_sub e2 x1 t1) (tt_sub t2 x1 t1)
  end.

(******************************************************************)
(* Substituting a non-free variable of a term/type has no effect. *)
(******************************************************************)

Theorem ttt_sub_bound :
  forall t1 t2 x,
  ~ In x (t_free_vars t1) ->
  tt_sub t1 x t2 = t1.
Proof.
  induction t1; search.
Qed.

#[export] Hint Resolve ttt_sub_bound : main.

Theorem eee_sub_bound :
  forall e1 e2 x,
  ~ In x (ee_free_vars e1) ->
  ee_sub e1 x e2 = e1.
Proof.
  induction e1; search.
Qed.

#[export] Hint Resolve eee_sub_bound : main.

Theorem eet_sub_bound :
  forall e t x,
  ~ In x (et_free_vars e) ->
  et_sub e x t = e.
Proof.
  induction e; search; clean; f_equal; search; apply ttt_sub_bound; search.
Qed.

#[export] Hint Resolve eet_sub_bound : main.

(*****************************************)
(* Substitution preserves local closure. *)
(*****************************************)

Theorem tt_sub_locally_closed :
  forall i t1 t2 x,
  TLocallyClosed t1 i ->
  TLocallyClosed t2 i ->
  TLocallyClosed (tt_sub t1 x t2) i.
Proof.
  clean. outro i. induction t1; search; clean; invert H; search.
  constructor. apply IHt1; search.
  apply t_local_closure_monotonic with (i1 := i); search.
Qed.

#[export] Hint Resolve tt_sub_locally_closed : main.

Theorem ee_sub_locally_closed :
  forall e1 e2 ie it x,
  ELocallyClosed e1 ie it ->
  ELocallyClosed e2 ie it ->
  ELocallyClosed (ee_sub e1 x e2) ie it.
Proof.
  clean. outro ie it. induction e1; search; clean; invert H; search;
    constructor; search; apply IHe1; search;
    apply e_local_closure_monotonic with (ie1 := ie) (it1 := it); search.
Qed.

#[export] Hint Resolve ee_sub_locally_closed : main.

Theorem et_sub_locally_closed :
  forall e ie it t x,
  ELocallyClosed e ie it ->
  TLocallyClosed t it ->
  ELocallyClosed (et_sub e x t) ie it.
Proof.
  clean. outro ie it. induction e; search; clean; invert H; search.
  constructor. apply IHe; search.
  apply t_local_closure_monotonic with (i1 := it); search.
Qed.

#[export] Hint Resolve et_sub_locally_closed : main.

(************************************)
(* Free variables of a substitution *)
(************************************)

#[local] Theorem incl_app_remove_weakening_left :
  forall x l1 l2 l3,
  incl (l1 ++ remove name_eq x l2) (l1 ++ remove name_eq x (l2 ++ l3)).
Proof.
  unfold incl. clean.
  pose proof (in_app_or l1 (remove name_eq x l2) a H).
  destruct H0; search.
  apply in_or_app. right.
  induction l2; search.
Qed.

#[local] Hint Resolve incl_app_remove_weakening_left : main.

#[local] Theorem incl_app_remove_weakening_right :
  forall x l1 l2 l3,
  incl (l1 ++ remove name_eq x l3) (l1 ++ remove name_eq x (l2 ++ l3)).
Proof.
  unfold incl. clean.
  pose proof (in_app_or l1 (remove name_eq x l3) a H).
  destruct H0; search.
  apply in_or_app. right.
  induction l2; search.
Qed.

#[local] Hint Resolve incl_app_remove_weakening_right : main.

Theorem ttt_free_sub :
  forall t1 t2 x,
  incl
    (t_free_vars (tt_sub t1 x t2))
    (t_free_vars t2 ++ remove name_eq x (t_free_vars t1)).
Proof.
  clean. induction t1; search. clean. apply incl_app.
  - apply incl_tran with (
      m := t_free_vars t2 ++ remove name_eq x (t_free_vars t1_1)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t2 ++ remove name_eq x (t_free_vars t1_2)
    ); search.
Qed.

#[export] Hint Resolve ttt_free_sub : main.

Theorem eeee_free_sub :
  forall e1 e2 x,
  incl
    (ee_free_vars (ee_sub e1 x e2))
    (ee_free_vars e2 ++ remove name_eq x (ee_free_vars e1)).
Proof.
  clean. induction e1; search. clean. apply incl_app.
  - apply incl_tran with (
      m := ee_free_vars e2 ++ remove name_eq x (ee_free_vars e1_1)
    ); search.
  - apply incl_tran with (
      m := ee_free_vars e2 ++ remove name_eq x (ee_free_vars e1_2)
    ); search.
Qed.

#[export] Hint Resolve eeee_free_sub : main.

Theorem eeet_free_sub :
  forall e t x,
  incl (ee_free_vars (et_sub e x t)) (ee_free_vars e).
Proof.
  clean. induction e; search.
Qed.

#[export] Hint Resolve eeet_free_sub : main.

Theorem etee_free_sub :
  forall e1 e2 x,
  incl (et_free_vars (ee_sub e1 x e2)) (et_free_vars e2 ++ et_free_vars e1).
Proof.
  clean. induction e1; search; clean; apply incl_app.
  - apply incl_tran with (m := et_free_vars e2 ++ t_free_vars t); search.
  - apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1); search.
  - apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1_1); search.
  - apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1_2); search.
  - apply incl_tran with (m := et_free_vars e2 ++ et_free_vars e1); search.
  - apply incl_tran with (m := et_free_vars e1 ++ t_free_vars t); search.
Qed.

#[export] Hint Resolve etee_free_sub : main.

Theorem etet_free_sub :
  forall e t x,
  incl
    (et_free_vars (et_sub e x t))
    (t_free_vars t ++ remove name_eq x (et_free_vars e)).
Proof.
  clean. induction e; search; clean; apply incl_app.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (t_free_vars t0)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (et_free_vars e)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (et_free_vars e1)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (et_free_vars e2)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (et_free_vars e)
    ); search.
  - apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (t_free_vars t0)
    ); search.
Qed.

#[export] Hint Resolve etet_free_sub : main.
