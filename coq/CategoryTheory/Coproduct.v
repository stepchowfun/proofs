(************************)
(************************)
(****                ****)
(****   Coproducts   ****)
(****                ****)
(************************)
(************************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Product.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariable for coproducts: x_y *)
(* Metavariables for injections: ix, iy *)

Definition coproduct
  {C : category}
  (x y x_y : object C)
  (ix : arrow C x x_y)
  (iy : arrow C y x_y)
:=
  forall
    (z : object C)
    (qx : arrow C x z)
    (qy : arrow C y z),
  arrowExistsUnique (
    fun f => qx = compose C f ix /\ qy = compose C f iy
  ).

Theorem opProductCoproduct :
  forall C x y xy px py,
  @coproduct C x y xy px py <->
  @product (oppositeCategory C) x y xy px py.
Proof.
  magic.
Qed.

Hint Resolve opProductCoproduct.
