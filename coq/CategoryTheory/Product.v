(**********************)
(**********************)
(****              ****)
(****   Products   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Object.
Require Import Main.Tactics.

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

Theorem productUnique :
  forall C (x y : object C),
  objectUnique (fun xy => exists px py, product x y xy px py).
Proof.
  clean.
  unfold objectUnique. unfold product. clean.
  fact (H y0 x1 x2). fact (H0 x0 x3 x4). fact (H x0 x3 x4). fact (H0 y0 x1 x2).
  clear H H0.
  unfold arrowExistsUnique in *. clean. clear H H3 H5 H6.
  unfold arrowExists in *. destruct H1. destruct H. destruct H2. destruct H2.
  unfold isomorphic. unfold isomorphism. exists x6. exists x5.
  unfold arrowUnique in *.
  split.
  - apply H4; magic.
    split; rewrite cAssoc; magic.
  - apply H0; magic.
    split; rewrite cAssoc; magic.
Qed.

Hint Resolve productUnique.
