(********************************)
(********************************)
(****                        ****)
(****   Product categories   ****)
(****                        ****)
(********************************)
(********************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

Set Universe Polymorphism.

Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

Definition productCategory (C D : category) : category.
Proof.
  refine (newCategory
    (object C * object D)
    (fun x y => arrow C (fst x) (fst y) * arrow D (snd x) (snd y))
    (fun {x y z} f g => (compose C (fst f) (fst g), compose D (snd f) (snd g)))
    (fun {x} => (id C, id D))
    _ _ _
  ); magic.
Defined.

Definition productCategoryProj1 (C D : category) :
  @functor (productCategory C D) C.
Proof.
  refine (newFunctor (productCategory C D) C
    fst
    (fun _ _ => fst)
    _
    _
  ); magic.
Defined.

Definition productCategoryProj2 (C D : category) :
  @functor (productCategory C D) D.
Proof.
  refine (newFunctor (productCategory C D) D
    snd
    (fun _ _ => snd)
    _
    _
  ); magic.
Defined.
