(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   A proof that cartesian products are categorical products in SET   ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Examples.Set.
Require Import Main.CategoryTheory.Product.
Require Import Main.Tactics.

Theorem cartesianProduct (x y : Set) :
  @product setCategory x y (x * y) fst snd.
Proof.
  unfold product.
  clean.
  unfold arrowExistsUnique.
  split.
  - exists (fun w => (qx w, qy w)). magic.
  - unfold arrowUnique.
    intros.
    destruct H.
    destruct H0.
    apply functional_extensionality.
    intro.
    apply injective_projections.
    + replace (fst (f x0)) with (qx x0); [idtac | magic].
      replace (fst (g x0)) with (qx x0); [magic | rewrite H0; magic].
    + replace (snd (f x0)) with (qy x0); [idtac | magic].
      replace (snd (g x0)) with (qy x0); [magic | rewrite H2; magic].
Qed.
