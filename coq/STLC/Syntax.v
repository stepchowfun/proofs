(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import Main.STLC.Name.

Import Name.

Inductive term : Set :=
| eTrue : term
| eFalse : term
| eIf : term -> term -> term -> term
| eVar : name -> term
| eAbs : name -> type -> term -> term
| eApp : term -> term -> term

with type : Set :=
| tBool : type
| tArrow : type -> type -> type.
