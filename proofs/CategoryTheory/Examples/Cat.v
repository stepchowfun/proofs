(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   The category of categories and functors   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.

Program Definition catCategory : category := {|
  object := category;
  arrow := functor;
  id := idFunctor;
  compose := compFunctor;
|}.
