(************************)
(************************)
(****                ****)
(****   Coproducts   ****)
(****                ****)
(************************)
(************************)

Require Import Coq.Classes.Morphisms.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Initial.
Require Import Main.CategoryTheory.Object.
Require Import Main.CategoryTheory.Product.
Require Import Main.CategoryTheory.Terminal.
Require Import Main.Tactics.

#[local] Set Universe Polymorphism.

(* Metavariable for coproducts: `xy` (same as products) *)
(* Metavariables for injections: `ix`, `iy` *)

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
  search.
Qed.

#[export] Hint Resolve opCoproductProduct : main.

Theorem opProductCoproduct C x y xy px py :
  @product C x y xy px py <-> @coproduct (oppositeCategory C) x y xy px py.
Proof.
  search.
Qed.

#[export] Hint Resolve opProductCoproduct : main.

Theorem coproductUnique C (x y : object C) :
  uniqueUpToIsomorphism (fun xy => exists ix iy, coproduct x y xy ix iy).
Proof.
  unfold uniqueUpToIsomorphism.
  clean.
  rewrite opCoproductProduct in *.
  rewrite opIsomorphic.
  pose proof (productUnique (oppositeCategory C) x y y0 x0).
  eSearch.
Qed.

#[export] Hint Resolve coproductUnique : main.

Theorem coproductCommutator
  {C}
  (x y xy : object C)
  (ix : arrow x xy)
  (iy : arrow y xy)
: coproduct x y xy ix iy -> coproduct y x xy iy ix.
Proof.
  repeat rewrite opCoproductProduct.
  apply productCommutator.
Qed.

(*
  We deliberately avoid adding a resolve hint for `coproductCommutator` because
  doing so could lead to nonterminating searches.
*)

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

#[export] Hint Resolve coproductCommutative : main.

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

#[export] Hint Resolve coproductAssociative : main.

Theorem coproductInitial
  {C}
  (x y xy : object C)
  (x_to_xy : arrow x xy)
  (y_to_xy : arrow y xy)
: coproduct x y xy x_to_xy y_to_xy -> initial x -> isomorphic y xy.
Proof.
  rewrite opCoproductProduct.
  rewrite opInitialTerminal.
  rewrite opIsomorphic.
  apply productTerminal.
Qed.

#[export] Hint Resolve coproductInitial : main.
