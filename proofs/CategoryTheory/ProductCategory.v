(********************************)
(********************************)
(****                        ****)
(****   Product categories   ****)
(****                        ****)
(********************************)
(********************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.
#[local] Set Universe Polymorphism.

#[local] Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

Program Definition productCategory C D : category := {|
  object := object C * object D;
  arrow x y := arrow (fst x) (fst y) * arrow (snd x) (snd y);
  id x := (id (fst x), id (snd x));
  compose _ _ _ f g := (compose (fst f) (fst g), compose (snd f) (snd g));
|}.

Program Definition productCategoryProj1 C D : functor (productCategory C D) C
:= {|
  oMap := fst;
  fMap _ _ := fst;
|}.

Program Definition productCategoryProj2 C D : functor (productCategory C D) D
:= {|
  oMap := snd;
  fMap _ _ := snd;
|}.
