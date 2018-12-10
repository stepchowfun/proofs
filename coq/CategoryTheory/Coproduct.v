(************************)
(************************)
(****                ****)
(****   Coproducts   ****)
(****                ****)
(************************)
(************************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Object.
Require Import Main.CategoryTheory.Product.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariable for coproducts: xy (same as products) *)
(* Metavariables for injections: ix, iy *)

Definition coproduct
  {C : category}
  (x y xy : object C)
  (ix : arrow C x xy)
  (iy : arrow C y xy)
:=
  forall
    (z : object C)
    (qx : arrow C x z)
    (qy : arrow C y z),
  universal (fun f => qx = compose C f ix /\ qy = compose C f iy).

Theorem opCoproductProduct C x y xy px py :
  @coproduct C x y xy px py <-> @product (oppositeCategory C) x y xy px py.
Proof.
  magic.
Qed.

Hint Resolve opCoproductProduct.

Theorem opProductCoproduct C x y xy px py :
  @product C x y xy px py <-> @coproduct (oppositeCategory C) x y xy px py.
Proof.
  magic.
Qed.

Hint Resolve opProductCoproduct.

Theorem coproductUnique C (x y : object C) :
  uniqueUpToIsomorphism (fun xy => exists ix iy, coproduct x y xy ix iy).
Proof.
  unfold uniqueUpToIsomorphism.
  clean.
  rewrite opCoproductProduct in *.
  rewrite opIsomorphic.
  fact (productUnique (oppositeCategory C) x y y0 x0).
  eMagic.
Qed.

Hint Resolve coproductUnique.

Theorem coproductCommutative
  {C : category}
  (x y xy yx : object C)
  (ix1 : arrow C x xy)
  (iy1 : arrow C y xy)
  (ix2 : arrow C x yx)
  (iy2 : arrow C y yx)
: coproduct x y xy ix1 iy1 -> coproduct y x yx iy2 ix2 -> isomorphic yx xy.
Proof.
  repeat rewrite opCoproductProduct.
  rewrite opIsomorphic.
  apply productCommutative.
Qed.

Hint Resolve coproductCommutative.

Theorem coproductAssociative
  {C : category}
  (x y z xy yz xy_z x_yz : object C)
  (x_to_xy : arrow C x xy)
  (y_to_xy : arrow C y xy)
  (y_to_yz : arrow C y yz)
  (z_to_yz : arrow C z yz)
  (xy_to_xy_z : arrow C xy xy_z)
  (z_to_xy_z : arrow C z xy_z)
  (x_to_x_yz : arrow C x x_yz)
  (yz_to_x_yz : arrow C yz x_yz)
: coproduct x y xy x_to_xy y_to_xy ->
  coproduct y z yz y_to_yz z_to_yz ->
  coproduct xy z xy_z xy_to_xy_z z_to_xy_z ->
  coproduct x yz x_yz x_to_x_yz yz_to_x_yz ->
  isomorphic x_yz xy_z.
Proof.
  repeat rewrite opCoproductProduct.
  rewrite opIsomorphic.
  apply productAssociative.
Qed.

Hint Resolve coproductAssociative.
