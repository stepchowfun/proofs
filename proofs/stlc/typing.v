(**************************)
(**************************)
(****                  ****)
(****   Typing rules   ****)
(****                  ****)
(**************************)
(**************************)

Require Import main.stlc.name.
Require Import main.stlc.syntax.

Inductive Context :=
| c_empty : Context
| c_extend : Context -> Name -> Ty -> Context.

Fixpoint lookup c1 x1 :=
  match c1 with
  | c_empty => None
  | c_extend c2 x2 t => if name_eq x1 x2 then Some t else lookup c2 x1
  end.

Inductive HasType : Context -> Term -> Ty -> Prop :=
| ht_true :
  forall c,
  HasType c e_true t_bool
| ht_false :
  forall c,
  HasType c e_false t_bool
| ht_if :
  forall c e1 e2 e3 t,
  HasType c e1 t_bool ->
  HasType c e2 t ->
  HasType c e3 t ->
  HasType c (e_if e1 e2 e3) t
| ht_var :
  forall c t x,
  lookup c x = Some t ->
  HasType c (e_var x) t
| ht_abs :
  forall c e t1 t2 x,
  HasType (c_extend c x t2) e t1 ->
  HasType c (e_abs x t2 e) (t_arrow t2 t1)
| ht_app :
  forall c e1 e2 t1 t2,
  HasType c e1 (t_arrow t2 t1) ->
  HasType c e2 t2 ->
  HasType c (e_app e1 e2) t1.

#[export] Hint Constructors HasType : main.
