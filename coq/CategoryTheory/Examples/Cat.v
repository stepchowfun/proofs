(******************************************************************)
(******************************************************************)
(****                                                          ****)
(****   A proof that categories and functors form a category   ****)
(****                                                          ****)
(******************************************************************)
(******************************************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import ProofIrrelevance.

Let catCAssoc
  (w x y z : category)
  (f : @functor w x)
  (g : @functor x y)
  (h : @functor y z)
: compFunctor h (compFunctor g f) = compFunctor (compFunctor h g) f.
Proof.
  unfold compFunctor.
  f_equal; apply proof_irrelevance.
Qed.

Let catCIdentLeft (x y : category) (f : @functor x y) :
  compFunctor idFunctor f = f.
Proof.
  unfold compFunctor.
  destruct f.
  f_equal; apply proof_irrelevance.
Qed.

Let catCIdentRight (x y : category) (f : @functor x y) :
  compFunctor f idFunctor = f.
Proof.
  unfold compFunctor.
  destruct f.
  f_equal; apply proof_irrelevance.
Qed.

Definition catCategory : category := newCategory
  category
  (@functor)
  (fun _ _ _ => compFunctor)
  (fun _ => idFunctor)
  catCAssoc
  catCIdentLeft
  catCIdentRight.
