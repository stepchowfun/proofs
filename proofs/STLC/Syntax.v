(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import Main.STLC.Name.

Inductive term :=
| eTrue : term
| eFalse : term
| eIf : term -> term -> term -> term
| eVar : name -> term
| eAbs : name -> type -> term -> term
| eApp : term -> term -> term

with type :=
| tBool : type
| tArrow : type -> type -> type.
