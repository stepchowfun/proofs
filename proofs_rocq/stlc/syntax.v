(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import main.stlc.name.

Inductive Term :=
| e_true : Term
| e_false : Term
| e_if : Term -> Term -> Term -> Term
| e_var : Name -> Term
| e_abs : Name -> Ty -> Term -> Term
| e_app : Term -> Term -> Term

with Ty :=
| t_bool : Ty
| t_arrow : Ty -> Ty -> Ty.
