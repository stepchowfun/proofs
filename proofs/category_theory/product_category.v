(********************************)
(********************************)
(****                        ****)
(****   Product categories   ****)
(****                        ****)
(********************************)
(********************************)

Require Import main.category_theory.category.
Require Import main.category_theory.functor.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

#[local] Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

Program Definition product_category C D : Category := {|
  Object := Object C * Object D;
  Arrow x y := Arrow (fst x) (fst y) * Arrow (snd x) (snd y);
  id x := (id (fst x), id (snd x));
  compose _ _ _ f g := (compose (fst f) (fst g), compose (snd f) (snd g));
|}.

Program Definition product_category_proj1 C D
: Functor (product_category C D) C
:= {|
  o_map := fst;
  f_map _ _ := fst;
|}.

Program Definition product_category_proj2 C D
: Functor (product_category C D) D
:= {|
  o_map := snd;
  f_map _ _ := snd;
|}.
