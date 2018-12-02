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

Let productCategoryCAssoc
  {C D : category}
  (w x y z : object C * object D)
  (f : arrow C (fst w) (fst x) * arrow D (snd w) (snd x))
  (g : arrow C (fst x) (fst y) * arrow D (snd x) (snd y))
  (h : arrow C (fst y) (fst z) * arrow D (snd y) (snd z))
: (
    compose C
      (fst h)
      (fst (compose C (fst g) (fst f), compose D (snd g) (snd f))),
    compose D
      (snd h)
      (snd (compose C (fst g) (fst f), compose D (snd g) (snd f)))
  ) = (
    compose C
      (fst (compose C (fst h) (fst g), compose D (snd h) (snd g)))
      (fst f),
    compose D
      (snd (compose C (fst h) (fst g), compose D (snd h) (snd g)))
      (snd f)
  ).
Proof.
  magic.
Qed.

Let productCategoryCIdentLeft
  {C D : category}
  (x y : object C * object D)
  (f : arrow C (fst x) (fst y) * arrow D (snd x) (snd y))
: (
    compose C (fst (@id C (fst y), @id D (snd y))) (fst f),
    compose D (snd (@id C (fst y), @id D (snd y))) (snd f)
  ) = f.
Proof.
  magic.
Qed.

Let productCategoryCIdentRight
  {C D : category}
  (x y : object C * object D)
  (f : arrow C (fst x) (fst y) * arrow D (snd x) (snd y))
: (
    compose C (fst f) (fst (@id C (fst x), @id D (snd x))),
    compose D (snd f) (snd (@id C (fst x), @id D (snd x)))
  ) = f.
Proof.
  magic.
Qed.

Definition productCategory (C D : category) : category := newCategory
  (object C * object D)
  (fun x y => arrow C (fst x) (fst y) * arrow D (snd x) (snd y))
  (fun {x y z} f g => (compose C (fst f) (fst g), compose D (snd f) (snd g)))
  (fun {x} => (id C, id D))
  productCategoryCAssoc
  productCategoryCIdentLeft
  productCategoryCIdentRight.

Let productCategoryProj1FIdent
  {C D : category}
  (x : object (productCategory C D))
: fst (@id (productCategory C D) x) = id C.
Proof.
  magic.
Qed.

Let productCategoryProj1FComp
  {C D : category}
  (x y z : object (productCategory C D))
  (f : arrow (productCategory C D) x y)
  (g : arrow (productCategory C D) y z)
: compose C (fst g) (fst f) = fst (compose (productCategory C D) g f).
Proof.
  magic.
Qed.

Definition productCategoryProj1 (C D : category) :
  @functor (productCategory C D) C := newFunctor
    (productCategory C D)
    C
    fst
    (fun _ _ => fst) productCategoryProj1FIdent productCategoryProj1FComp.

Let productCategoryProj2FIdent
  {C D : category}
  (x : object (productCategory C D))
: snd (@id (productCategory C D) x) = id D.
Proof.
  magic.
Qed.

Let productCategoryProj2FComp
  {C D : category}
  (x y z : object (productCategory C D))
  (f : arrow (productCategory C D) x y)
  (g : arrow (productCategory C D) y z)
: compose D (snd g) (snd f) = snd (compose (productCategory C D) g f).
Proof.
  magic.
Qed.

Definition productCategoryProj2 (C D : category) :
  @functor (productCategory C D) D := newFunctor
    (productCategory C D)
    D
    snd
    (fun _ _ => snd) productCategoryProj2FIdent productCategoryProj2FComp.
