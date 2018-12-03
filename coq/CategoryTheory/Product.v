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
  universal (fun f => qx = compose C px f /\ qy = compose C py f).

Theorem productUnique C (x y : object C) :
  uniqueUpToIsomorphism (fun xy => exists px py, product x y xy px py).
Proof.
  clean.
  unfold uniqueUpToIsomorphism. unfold product. clean.
  fact (H y0 x1 x2). fact (H0 x0 x3 x4). fact (H x0 x3 x4). fact (H0 y0 x1 x2).
  clear H H0.
  unfold universal in *. clean. clear H H3 H5 H6.
  unfold arrowExists in *. destruct H1. destruct H. destruct H2. destruct H2.
  unfold isomorphic. unfold isomorphism. unfold inverse. exists x6. exists x5.
  unfold arrowUnique in *.
  split.
  - apply H0; magic.
    split; rewrite cAssoc; magic.
  - apply H4; magic.
    split; rewrite cAssoc; magic.
Qed.

Hint Resolve productUnique.

Theorem productCommutator
  {C : category}
  (x y xy : object C)
  (px : arrow C xy x)
  (py : arrow C xy y)
: product x y xy px py -> product y x xy py px.
Proof.
  unfold product.
  unfold universal.
  unfold arrowExists.
  unfold arrowUnique.
  clean.
  specialize (H z qy qx).
  eMagic.
Qed.

(*
  We deliberately avoid adding a resolve hint for productCommutator because
  doing so could lead to nonterminating searches.
*)

Theorem productCommutative
  {C : category}
  (x y xy yx : object C)
  (px1 : arrow C xy x)
  (py1 : arrow C xy y)
  (px2 : arrow C yx x)
  (py2 : arrow C yx y)
: product x y xy px1 py1 -> product y x yx py2 px2 -> isomorphic xy yx.
Proof.
  clean.
  apply productCommutator in H0.
  fact (productUnique C x y).
  unfold uniqueUpToIsomorphism in H1.
  apply H1; eMagic.
Qed.

Hint Resolve productCommutative.
