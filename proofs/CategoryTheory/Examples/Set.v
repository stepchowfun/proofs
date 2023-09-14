(************************************************)
(************************************************)
(****                                        ****)
(****   The category of sets and functions   ****)
(****                                        ****)
(************************************************)
(************************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Product.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.
#[local] Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

(* Sets and functions form a category. *)

Program Definition setCategory : category := {|
  object := Type;
  arrow x y := x -> y;
  id _ := fun x => x;
  compose _ _ _ f g := fun x => g (f x);
|}.

(* Cartesian products are categorical products in this category. *)

Theorem cartesianProduct x y :
  @product setCategory x y (x * y) fst snd.
Proof.
  unfold product.
  clean.
  unfold universal.
  split.
  - exists (fun w => (qx w, qy w)). search.
  - unfold arrowUnique.
    intros.
    destruct H.
    destruct H0.
    apply functional_extensionality.
    intros.
    apply injective_projections.
    + replace (fst (f x0)) with (qx x0); [idtac | search].
      replace (fst (g x0)) with (qx x0); [search | rewrite H0; search].
    + replace (snd (f x0)) with (qy x0); [idtac | search].
      replace (snd (g x0)) with (qy x0); [search | rewrite H2; search].
Qed.
