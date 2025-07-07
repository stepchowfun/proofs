(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Stdlib.Lists.List.
Require Import main.system_f.syntax.

Import Stdlib.Lists.List.ListNotations.

Fixpoint ee_free_vars e1 :=
  match e1 with
  | e_free_var x => [x]
  | e_bound_var _ => []
  | e_abs _ e2 => ee_free_vars e2
  | e_app e2 e3 => ee_free_vars e2 ++ ee_free_vars e3
  | e_t_abs e2 => ee_free_vars e2
  | e_t_app e2 _ => ee_free_vars e2
  end.

Fixpoint t_free_vars t1 :=
  match t1 with
  | t_free_var x => [x]
  | t_bound_var _ => []
  | t_arrow t2 t3 => t_free_vars t2 ++ t_free_vars t3
  | t_for_all t2 => t_free_vars t2
  end.

Fixpoint et_free_vars e1 :=
  match e1 with
  | e_free_var x => []
  | e_bound_var _ => []
  | e_abs t e2 => t_free_vars t ++ et_free_vars e2
  | e_app e2 e3 => et_free_vars e2 ++ et_free_vars e3
  | e_t_abs e2 => et_free_vars e2
  | e_t_app e2 t => et_free_vars e2 ++ t_free_vars t
  end.
