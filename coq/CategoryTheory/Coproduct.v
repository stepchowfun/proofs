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
  {C}
  (x y xy : object C)
  (ix : arrow x xy)
  (iy : arrow y xy)
:=
  forall z (qx : arrow x z) (qy : arrow y z),
  universal (fun f => qx = compose f ix /\ qy = compose f iy).

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
  {C}
  (x y xy yx : object C)
  (ix1 : arrow x xy)
  (iy1 : arrow y xy)
  (ix2 : arrow x yx)
  (iy2 : arrow y yx)
: coproduct x y xy ix1 iy1 -> coproduct y x yx iy2 ix2 -> isomorphic yx xy.
Proof.
  repeat rewrite opCoproductProduct.
  rewrite opIsomorphic.
  apply productCommutative.
Qed.

Hint Resolve coproductCommutative.

Theorem coproductAssociative
  {C}
  (x y z xy yz xy_z x_yz : object C)
  (x_to_xy : arrow x xy)
  (y_to_xy : arrow y xy)
  (y_to_yz : arrow y yz)
  (z_to_yz : arrow z yz)
  (xy_to_xy_z : arrow xy xy_z)
  (z_to_xy_z : arrow z xy_z)
  (x_to_x_yz : arrow x x_yz)
  (yz_to_x_yz : arrow yz x_yz)
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
