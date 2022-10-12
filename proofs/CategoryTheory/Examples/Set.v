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

#[local] Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

(* Sets and functions form a category. *)

#[local] Theorem setCAssoc w x y z (f : w -> x) (g : x -> y) (h : y -> z) :
  (fun e : w => h (g (f e))) = (fun e : w => h (g (f e))).
Proof.
  search.
Qed.

#[local] Theorem setCIdent x y (f : x -> y) : (fun e : x => f e) = f.
Proof.
  search.
Qed.

Definition setCategory : category := newCategory
  Type
  (fun x y => x -> y)
  (fun _ _ _ f g e => f (g e))
  (fun x e => e)
  setCAssoc setCIdent setCIdent.

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
