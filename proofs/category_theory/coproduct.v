(************************)
(************************)
(****                ****)
(****   Coproducts   ****)
(****                ****)
(************************)
(************************)

Require Import Coq.Classes.Morphisms.
Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.category_theory.initial.
Require Import main.category_theory.object.
Require Import main.category_theory.product.
Require Import main.category_theory.terminal.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

(* Metavariable for coproducts: `xy` (same as products) *)
(* Metavariables for injections: `ix`, `iy` *)

Definition coproduct
  [C]
  (x y xy : Object C)
  (ix : Arrow x xy)
  (iy : Arrow y xy)
:=
  forall z (qx : Arrow x z) (qy : Arrow y z),
  Universal (fun f => qx = compose ix f /\ qy = compose iy f).

Theorem op_coproduct_product C x y xy px py :
  @coproduct C x y xy px py <-> @product (opposite_category C) x y xy px py.
Proof.
  search.
Qed.

#[export] Hint Resolve op_coproduct_product : main.

Theorem op_product_coproduct C x y xy px py :
  @product C x y xy px py <-> @coproduct (opposite_category C) x y xy px py.
Proof.
  search.
Qed.

#[export] Hint Resolve op_product_coproduct : main.

Theorem coproduct_unique C (x y : Object C) :
  UniqueUpToIsomorphism (fun xy => exists ix iy, coproduct x y xy ix iy).
Proof.
  unfold UniqueUpToIsomorphism.
  clean.
  rewrite op_coproduct_product in *.
  rewrite op_isomorphic.
  pose proof (product_unique (opposite_category C) x y y0 x0).
  esearch.
Qed.

#[export] Hint Resolve coproduct_unique : main.

Theorem coproduct_commutator
  [C]
  (x y xy : Object C)
  (ix : Arrow x xy)
  (iy : Arrow y xy)
: coproduct x y xy ix iy -> coproduct y x xy iy ix.
Proof.
  repeat rewrite op_coproduct_product.
  apply product_commutator.
Qed.

(*
  We deliberately avoid adding a resolve hint for `coproduct_commutator`
  because doing so could lead to nonterminating searches.
*)

Theorem coproduct_commutative
  [C]
  (x y xy yx : Object C)
  (ix1 : Arrow x xy)
  (iy1 : Arrow y xy)
  (ix2 : Arrow x yx)
  (iy2 : Arrow y yx)
: coproduct x y xy ix1 iy1 -> coproduct y x yx iy2 ix2 -> Isomorphic yx xy.
Proof.
  repeat rewrite op_coproduct_product.
  rewrite op_isomorphic.
  apply product_commutative.
Qed.

#[export] Hint Resolve coproduct_commutative : main.

Theorem coproduct_associative
  [C]
  (x y z xy yz xy_z x_yz : Object C)
  (x_to_xy : Arrow x xy)
  (y_to_xy : Arrow y xy)
  (y_to_yz : Arrow y yz)
  (z_to_yz : Arrow z yz)
  (xy_to_xy_z : Arrow xy xy_z)
  (z_to_xy_z : Arrow z xy_z)
  (x_to_x_yz : Arrow x x_yz)
  (yz_to_x_yz : Arrow yz x_yz)
: coproduct x y xy x_to_xy y_to_xy ->
  coproduct y z yz y_to_yz z_to_yz ->
  coproduct xy z xy_z xy_to_xy_z z_to_xy_z ->
  coproduct x yz x_yz x_to_x_yz yz_to_x_yz ->
  Isomorphic x_yz xy_z.
Proof.
  repeat rewrite op_coproduct_product.
  rewrite op_isomorphic.
  apply product_associative.
Qed.

#[export] Hint Resolve coproduct_associative : main.

Theorem coproduct_initial
  [C]
  (x y xy : Object C)
  (x_to_xy : Arrow x xy)
  (y_to_xy : Arrow y xy)
: coproduct x y xy x_to_xy y_to_xy -> initial x -> Isomorphic y xy.
Proof.
  rewrite op_coproduct_product.
  rewrite op_initial_terminal.
  rewrite op_isomorphic.
  apply product_terminal.
Qed.

#[export] Hint Resolve coproduct_initial : main.
