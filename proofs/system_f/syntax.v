(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import main.system_f.name.

Inductive Term :=
| e_free_var : Name -> Term
| e_bound_var : nat -> Term
| e_abs : Ty -> Term -> Term
| e_app : Term -> Term -> Term
| e_t_abs : Term -> Term
| e_t_app : Term -> Ty -> Term

with Ty :=
| t_free_var : Name -> Ty
| t_bound_var : nat -> Ty
| t_arrow : Ty -> Ty -> Ty
| t_for_all : Ty -> Ty.
