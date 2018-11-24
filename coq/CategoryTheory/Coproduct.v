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
  universal (fun f => qx = compose C f ix /\ qy = compose C f iy).

Theorem opCoproductProduct :
  forall C x y xy px py,
  @coproduct C x y xy px py <->
  @product (oppositeCategory C) x y xy px py.
Proof.
  magic.
Qed.

Hint Resolve opCoproductProduct.

Theorem opProductCoproduct :
  forall C x y xy px py,
  @product C x y xy px py <->
  @coproduct (oppositeCategory C) x y xy px py.
Proof.
  magic.
Qed.

Hint Resolve opProductCoproduct.

Theorem coproductUnique :
  forall C (x y : object C),
  uniqueUpToIsomorphism (fun x_y => exists ix iy, coproduct x y x_y ix iy).
Proof.
  unfold uniqueUpToIsomorphism.
  clean.
  rewrite opCoproductProduct in *.
  rewrite opIsomorphic.
  rewrite isomorphicSymm.
  fact (productUnique (oppositeCategory C) x y x0 y0).
  eMagic.
Qed.

Hint Resolve coproductUnique.
