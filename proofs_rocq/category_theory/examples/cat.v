(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   The Category of categories and functors   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Require Import main.category_theory.category.
Require Import main.category_theory.functor.
Require Import main.tactics.

#[program] Definition cat_category : Category := {|
  Object := Category;
  Arrow := Functor;
  id := id_functor;
  compose := comp_functor;
|}.
