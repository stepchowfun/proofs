(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import Main.SystemF.Name.

Inductive term :=
| eFreeVar : name -> term
| eBoundVar : nat -> term
| eAbs : type -> term -> term
| eApp : term -> term -> term
| eTAbs : term -> term
| eTApp : term -> type -> term

with type :=
| tFreeVar : name -> type
| tBoundVar : nat -> type
| tArrow : type -> type -> type
| tForAll : type -> type.
