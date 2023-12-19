(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import main.stlc.name.
Require Import main.stlc.syntax.

Inductive Free_var : Term -> Name -> Prop :=
| fv_if1 :
  forall e1 e2 e3 x,
  Free_var e1 x ->
  Free_var (e_if e1 e2 e3) x
| fv_if2 :
  forall e1 e2 e3 x,
  Free_var e2 x ->
  Free_var (e_if e1 e2 e3) x
| fv_if3 :
  forall e1 e2 e3 x,
  Free_var e3 x ->
  Free_var (e_if e1 e2 e3) x
| fv_var :
  forall x,
  Free_var (e_var x) x
| fv_abs :
  forall e t x1 x2,
  Free_var e x1 ->
  x1 <> x2 ->
  Free_var (e_abs x2 t e) x1
| fv_app1 :
  forall e1 e2 x,
  Free_var e1 x ->
  Free_var (e_app e1 e2) x
| fv_app2 :
  forall e1 e2 x,
  Free_var e2 x ->
  Free_var (e_app e1 e2) x.

#[export] Hint Constructors Free_var : main.
