(**************************************)
(**************************************)
(****                              ****)
(****   Local closure predicates   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import main.system_f.syntax.
Require Import main.tactics.

Inductive TLocallyClosed : Ty -> nat -> Prop :=
| tlc_free_var :
  forall n x,
  TLocallyClosed (t_free_var x) n
| tlc_bound_var :
  forall n1 n2,
  n1 < n2 ->
  TLocallyClosed (t_bound_var n1) n2
| tlc_arrow :
  forall n t1 t2,
  TLocallyClosed t1 n ->
  TLocallyClosed t2 n ->
  TLocallyClosed (t_arrow t1 t2) n
| tlc_for_all :
  forall n t,
  TLocallyClosed t (S n) ->
  TLocallyClosed (t_for_all t) n.

#[export] Hint Constructors TLocallyClosed : main.

Inductive ELocallyClosed : Term -> nat -> nat -> Prop :=
| elc_free_var :
  forall ne nt x,
  ELocallyClosed (e_free_var x) ne nt
| elc_bound_var :
  forall ne1 ne2 nt,
  ne1 < ne2 ->
  ELocallyClosed (e_bound_var ne1) ne2 nt
| elc_abs :
  forall e ne nt t,
  TLocallyClosed t nt ->
  ELocallyClosed e (S ne) nt ->
  ELocallyClosed (e_abs t e) ne nt
| elc_app :
  forall e1 e2 ne nt,
  ELocallyClosed e1 ne nt ->
  ELocallyClosed e2 ne nt ->
  ELocallyClosed (e_app e1 e2) ne nt
| elc_t_abs :
  forall e ne nt,
  ELocallyClosed e ne (S nt) ->
  ELocallyClosed (e_t_abs e) ne nt
| elc_t_app :
  forall e ne nt t,
  ELocallyClosed e ne nt ->
  TLocallyClosed t nt ->
  ELocallyClosed (e_t_app e t) ne nt.

#[export] Hint Constructors ELocallyClosed : main.

(*************************************************)
(* Local closure is monotonic with the level(s). *)
(*************************************************)

Theorem t_local_closure_monotonic :
  forall i1 i2 t,
  i1 <= i2 ->
  TLocallyClosed t i1 ->
  TLocallyClosed t i2.
Proof.
  clean. outro i2 H. induction H0; search.
  clean. apply tlc_for_all. apply IHTLocallyClosed. search.
Qed.

(* Don't add a resolve hint because `eapply` has a hard time guessing `i1`. *)

Theorem e_local_closure_monotonic :
  forall e ie1 ie2 it1 it2,
  ie1 <= ie2 ->
  it1 <= it2 ->
  ELocallyClosed e ie1 it1 ->
  ELocallyClosed e ie2 it2.
Proof.
  clean. outro ie2 it2 H H0.
  induction H1; search; constructor; search; clean.
  - apply t_local_closure_monotonic with (i1 := nt); search.
  - apply IHELocallyClosed; search.
  - apply IHELocallyClosed; search.
  - apply t_local_closure_monotonic with (i1 := nt); search.
Qed.

(*
  Don't add a resolve hint because `eapply` has a hard time guessing
  `ie1`/`it1`.
*)
