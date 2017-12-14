(**********************)
(**********************)
(****              ****)
(****   Diagrams   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.

Set Universe Polymorphism.

(* Metavariables for diagrams: P *)

Record diagram {J C : category} := newDiagram {
  dFunctor : @functor J C;
}.

Definition commutative {J C : category} (P : @diagram J C) := thin J.
