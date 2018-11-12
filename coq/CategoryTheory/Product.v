(**********************)
(**********************)
(****              ****)
(****   Products   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.

Set Universe Polymorphism.

(* Metavariable for products: xy *)
(* Metavariables for projections: px, py *)

Definition product
  {C : category}
  (x y xy : object C)
  (px : arrow C xy x)
  (py : arrow C xy y)
:=
  forall
    (z : object C)
    (qx : arrow C z x)
    (qy : arrow C z y),
  arrowExistsUnique (
    fun f => qx = compose C px f /\ qy = compose C py f
  ).
