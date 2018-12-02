(************************************************)
(************************************************)
(****                                        ****)
(****   The category of sets and functions   ****)
(****                                        ****)
(************************************************)
(************************************************)

Require Import FunctionalExtensionality.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Product.
Require Import Main.Tactics.

Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

(* Sets and functions form a category. *)

Let setCAssoc (w x y z : Set) (f : w -> x) (g : x -> y) (h : y -> z):
  (fun e : w => h (g (f e))) = (fun e : w => h (g (f e))).
Proof.
  magic.
Qed.

Let setCIdent (x y : Set) (f : x -> y) : (fun e : x => f e) = f.
Proof.
  magic.
Qed.

Definition setCategory : category := newCategory
  Set
  (fun x y => x -> y)
  (fun x y z f g e => f (g e))
  (fun x e => e)
  setCAssoc setCIdent setCIdent.

(* Cartesian products are categorical products in this category. *)

Theorem cartesianProduct (x y : Set) :
  @product setCategory x y (x * y) fst snd.
Proof.
  unfold product.
  clean.
  unfold universal.
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
