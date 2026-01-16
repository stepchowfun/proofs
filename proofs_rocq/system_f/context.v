(*****************************)
(*****************************)
(****                     ****)
(****   Typing contexts   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import main.system_f.free_var.
Require Import main.system_f.local_closure.
Require Import main.system_f.name.
Require Import main.system_f.substitution.
Require Import main.system_f.syntax.
Require Import main.tactics.

Import Stdlib.Lists.List.ListNotations.

Inductive Context :=
| c_empty : Context
| c_e_extend : Context -> Name -> Ty -> Context
| c_t_extend : Context -> Name -> Context.

(*******************)
(* Variable lookup *)
(*******************)

Fixpoint e_lookup c1 x1 :=
  match c1 with
  | c_empty => None
  | c_e_extend c2 x2 t => if name_eq x1 x2 then Some t else e_lookup c2 x1
  | c_t_extend c2 _ => e_lookup c2 x1
  end.

Fixpoint t_lookup c1 x1 :=
  match c1 with
  | c_empty => false
  | c_e_extend c2 _ _ => t_lookup c2 x1
  | c_t_extend c2 x2 => if name_eq x1 x2 then true else t_lookup c2 x1
  end.

(***********)
(* Domains *)
(***********)

Fixpoint e_domain c1 :=
  match c1 with
  | c_empty => []
  | c_e_extend c2 x t => x :: e_domain c2
  | c_t_extend c2 _ => e_domain c2
  end.

Fixpoint t_domain c1 :=
  match c1 with
  | c_empty => []
  | c_e_extend c2 _ _ => t_domain c2
  | c_t_extend c2 x => x :: t_domain c2
  end.

(************************)
(* Type well-formedness *)
(************************)

Definition TWellFormed c t :=
  TLocallyClosed t 0 /\
  incl (t_free_vars t) (t_domain c).

(***************************)
(* Context well-formedness *)
(***************************)

Inductive CWellFormed : Context -> Prop :=
| cwf_empty :
  CWellFormed c_empty
| cwf_e_extend :
  forall c t x,
  ~ In x (e_domain c) ->
  TWellFormed c t ->
  CWellFormed c ->
  CWellFormed (c_e_extend c x t)
| cwf_t_extend :
  forall c x,
  ~ In x (t_domain c) ->
  CWellFormed c ->
  CWellFormed (c_t_extend c x).

Hint Constructors CWellFormed : main.

(*****************************)
(* Concatenation of contexts *)
(*****************************)

Fixpoint c_concat c1 c2 :=
  match c2 with
  | c_empty => c1
  | c_e_extend c3 x t2 => c_e_extend (c_concat c1 c3) x t2
  | c_t_extend c3 x => c_t_extend (c_concat c1 c3) x
  end.

(****************************)
(* Substitution on contexts *)
(****************************)

Fixpoint c_sub c1 x1 t1 :=
  match c1 with
  | c_empty => c_empty
  | c_e_extend c2 x2 t2 => c_e_extend (c_sub c2 x1 t1) x2 (tt_sub t2 x1 t1)
  | c_t_extend c2 x2 => c_t_extend (c_sub c2 x1 t1) x2
  end.

(***********************************)
(* Facts about domains and lookups *)
(***********************************)

Theorem e_domain_lookup :
  forall c x,
  In x (e_domain c) <-> exists t, e_lookup c x = Some t.
Proof.
  clean. split; induction c; esearch. clean. destruct H; esearch.
Qed.

Hint Resolve -> e_domain_lookup : main.
Hint Resolve <- e_domain_lookup : main.

Theorem t_domain_lookup :
  forall c x,
  In x (t_domain c) <-> t_lookup c x = true.
Proof.
  clean. induction c; search.
Qed.

Hint Resolve -> t_domain_lookup : main.
Hint Resolve <- t_domain_lookup : main.

(************************************)
(* Facts about type well-formedness *)
(************************************)

Theorem t_well_formed_closed :
  forall c t x,
  TWellFormed c t ->
  In x (t_free_vars t) ->
  In x (t_domain c).
Proof.
  clean. apply t_domain_lookup. invert H. search.
Qed.

Hint Resolve t_well_formed_closed : main.

Theorem t_lookup_well_formed :
  forall c x t,
  CWellFormed c ->
  e_lookup c x = Some t ->
  TWellFormed c t.
Proof.
  clean. unfold TWellFormed. induction H; search. clean.
  destruct (name_eq x x0); search. clean. invert H0. search.
Qed.

Hint Resolve t_lookup_well_formed : main.

(****************************)
(* Facts about substitution *)
(****************************)

Theorem c_sub_e_domain :
  forall c x t,
  e_domain (c_sub c x t) = e_domain c.
Proof.
  induction c; search.
Qed.

Hint Resolve c_sub_e_domain : main.

Theorem c_sub_t_domain :
  forall c x t,
  t_domain (c_sub c x t) = t_domain c.
Proof.
  induction c; search.
Qed.

Hint Resolve c_sub_t_domain : main.

(*****************************************)
(* Facts about concatenation of contexts *)
(*****************************************)

Theorem c_concat_empty : forall c, c_concat c_empty c = c.
Proof.
  induction c; search.
Qed.

Hint Resolve c_concat_empty : main.

Theorem c_concat_assoc :
  forall c1 c2 c3,
  c_concat (c_concat c1 c2) c3 = c_concat c1 (c_concat c2 c3).
Proof.
  induction c2; induction c3; search.
Qed.

Hint Resolve c_concat_assoc : main.

(*****************************************)
(* Facts about concatenation and domains *)
(*****************************************)

Theorem e_domain_concat :
  forall c1 c2,
  e_domain (c_concat c1 c2) = e_domain c2 ++ e_domain c1.
Proof.
  induction c2; search.
Qed.

Hint Resolve e_domain_concat : main.

Theorem t_domain_concat :
  forall c1 c2,
  t_domain (c_concat c1 c2) = t_domain c2 ++ t_domain c1.
Proof.
  induction c2; search.
Qed.

Hint Resolve t_domain_concat : main.

(****************************************)
(* Facts about concatenation and lookup *)
(****************************************)

Theorem c_concat_e_lookup :
  forall c1 c2 t x,
  e_lookup (c_concat c1 c2) x = Some t ->
  e_lookup c1 x = Some t \/ e_lookup c2 x = Some t.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_concat_e_lookup : main.

Theorem c_concat_t_lookup :
  forall c1 c2 x,
  t_lookup (c_concat c1 c2) x = true ->
  t_lookup c1 x = true \/ t_lookup c2 x = true.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_concat_t_lookup : main.

Theorem c_e_lookup_concat_right :
  forall c1 c2 t x,
  e_lookup c2 x = Some t ->
  e_lookup (c_concat c1 c2) x = Some t.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_e_lookup_concat_right : main.

Theorem c_e_lookup_concat_left :
  forall c1 c2 t x,
  e_lookup c1 x = Some t ->
  e_lookup c2 x = None ->
  e_lookup (c_concat c1 c2) x = Some t.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_e_lookup_concat_left : main.

Theorem c_t_lookup_concat_right :
  forall c1 c2 x,
  t_lookup c2 x = true ->
  t_lookup (c_concat c1 c2) x = true.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_t_lookup_concat_right : main.

Theorem c_t_lookup_concat_left :
  forall c1 c2 x,
  t_lookup c1 x = true ->
  t_lookup (c_concat c1 c2) x = true.
Proof.
  induction c2; search.
Qed.

Hint Resolve c_t_lookup_concat_left : main.

Theorem c_e_lookup_none :
  forall c1 c2 t x,
  e_lookup c1 x = Some t ->
  CWellFormed (c_concat c1 c2) ->
  e_lookup c2 x = None.
Proof.
  clean. induction c2; search; invert H0; feed IHc2; clean.
  destruct (name_eq x n); search. clean.
  assert (In n (e_domain c1)); esearch.
  rewrite e_domain_concat in H4.
  unfold not in H4. search.
Qed.

Hint Resolve c_e_lookup_none : main.

Theorem c_t_lookup_none :
  forall c1 c2 x,
  t_lookup c1 x = true ->
  CWellFormed (c_concat c1 c2) ->
  t_lookup c2 x = false.
Proof.
  clean. induction c2; search; invert H0; feed IHc2; clean.
  destruct (name_eq x n); search. clean.
  assert (In n (t_domain c1)); [esearch | idtac].
  rewrite t_domain_concat in H3.
  unfold not in H3. search.
Qed.

Hint Resolve c_t_lookup_none : main.

(***************************************)
(* Facts about context well-formedness *)
(***************************************)

Theorem c_well_formed_e_skip :
  forall c1 c2 t x,
  CWellFormed (c_concat (c_e_extend c1 x t) c2) ->
  CWellFormed (c_concat c1 c2).
Proof.
  clean. induction c2; invert H; search; clean; constructor; search.
  - rewrite e_domain_concat in *. clean.
    unfold not in *. clean.
    pose proof (in_app_or (e_domain c2) (e_domain c1) n H).
    destruct H0; search.
  - unfold TWellFormed in *. split; search. clean.
    rewrite t_domain_concat in *. search.
  - rewrite t_domain_concat in *. search.
Qed.

Hint Resolve c_well_formed_e_skip : main.

Theorem c_well_formed_t_skip :
  forall c1 c2 t x,
  CWellFormed (c_concat (c_t_extend c1 x) c2) ->
  TWellFormed c1 t ->
  CWellFormed (c_concat c1 (c_sub c2 x t)).
Proof.
  clean. induction c2; invert H; search; clean; constructor; search.
  - unfold TWellFormed in H5.
    rewrite e_domain_concat in *. rewrite c_sub_e_domain.
    unfold not in *. clean.
    assert (In n (e_domain c2) \/ In n (e_domain c1)); search.
  - unfold TWellFormed in *. split; search. clean.
    apply incl_tran with (
      m := t_free_vars t ++ remove name_eq x (t_free_vars t0)
    ); search.
    rewrite t_domain_concat. rewrite t_domain_concat in H1.
    assert (
      incl
        (remove name_eq x (t_free_vars t0))
        (t_domain (c_sub c2 x t) ++ t_domain c1)
    ); search.
    rewrite c_sub_t_domain.
    unfold incl in *. clean.
    specialize (H1 a). feed H1.
    + pose proof (name_in_remove (t_free_vars t0) a x H3). search.
    + pose proof (remove_In name_eq (t_free_vars t0) x).
      assert (a <> x); search. clear H5.
      pose proof (in_app_or (t_domain c2) (x :: t_domain c1) a H1).
      destruct H5; search.
  - rewrite t_domain_concat in *.
    unfold not in *. clean.
    assert (In n (t_domain (c_sub c2 x t)) \/ In n (t_domain c1)); search.
    destruct H1; search.
    rewrite c_sub_t_domain in H1. search.
Qed.

Hint Resolve c_well_formed_t_skip : main.
