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

#[local] Open Scope type. (* Parse `*` as `prod` rather than `mul`. *)

#[local] Theorem productCategoryCAssoc
  {C D}
  (w x y z : object C * object D)
  (f : arrow (fst w) (fst x) * arrow (snd w) (snd x))
  (g : arrow (fst x) (fst y) * arrow (snd x) (snd y))
  (h : arrow (fst y) (fst z) * arrow (snd y) (snd z))
: (
    compose
      (fst h)
      (fst (compose (fst g) (fst f), compose (snd g) (snd f))),
    compose
      (snd h)
      (snd (compose (fst g) (fst f), compose (snd g) (snd f)))
  ) = (
    compose
      (fst (compose (fst h) (fst g), compose (snd h) (snd g)))
      (fst f),
    compose
      (snd (compose (fst h) (fst g), compose (snd h) (snd g)))
      (snd f)
  ).
Proof.
  magic.
Qed.

#[local] Theorem productCategoryCIdentLeft
  {C D}
  (x y : object C * object D)
  (f : arrow (fst x) (fst y) * arrow (snd x) (snd y))
: (
    compose (fst (@id C (fst y), @id D (snd y))) (fst f),
    compose (snd (@id C (fst y), @id D (snd y))) (snd f)
  ) = f.
Proof.
  magic.
Qed.

#[local] Theorem productCategoryCIdentRight
  {C D : category}
  (x y : object C * object D)
  (f : arrow (fst x) (fst y) * arrow (snd x) (snd y))
: (
    compose (fst f) (fst (@id C (fst x), @id D (snd x))),
    compose (snd f) (snd (@id C (fst x), @id D (snd x)))
  ) = f.
Proof.
  magic.
Qed.

Definition productCategory C D : category := newCategory
  (object C * object D)
  (fun x y => arrow (fst x) (fst y) * arrow (snd x) (snd y))
  (fun _ _ _ f g => (compose (fst f) (fst g), compose (snd f) (snd g)))
  (fun _ => (id, id))
  productCategoryCAssoc
  productCategoryCIdentLeft
  productCategoryCIdentRight.

#[local] Theorem productCategoryProj1FIdent
  {C D}
  (x : object (productCategory C D))
: fst (@id (productCategory C D) x) = id.
Proof.
  magic.
Qed.

#[local] Theorem productCategoryProj1FComp
  {C D}
  (x y z : object (productCategory C D))
  (f : arrow x y)
  (g : arrow y z)
: compose (fst g) (fst f) = fst (compose g f).
Proof.
  magic.
Qed.

Definition productCategoryProj1 C D :
  functor (productCategory C D) C := newFunctor
    (productCategory C D)
    C
    fst
    (fun _ _ => fst) productCategoryProj1FIdent productCategoryProj1FComp.

#[local] Theorem productCategoryProj2FIdent
  {C D}
  (x : object (productCategory C D))
: snd (@id (productCategory C D) x) = id.
Proof.
  magic.
Qed.

#[local] Theorem productCategoryProj2FComp
  {C D}
  (x y z : object (productCategory C D))
  (f : arrow x y)
  (g : arrow y z)
: compose (snd g) (snd f) = snd (compose g f).
Proof.
  magic.
Qed.

Definition productCategoryProj2 C D :
  functor (productCategory C D) D := newFunctor
    (productCategory C D)
    D
    snd
    (fun _ _ => snd) productCategoryProj2FIdent productCategoryProj2FComp.
