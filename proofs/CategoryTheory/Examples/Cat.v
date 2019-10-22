(******************************************************************)
(******************************************************************)
(****                                                          ****)
(****   A proof that categories and functors form a category   ****)
(****                                                          ****)
(******************************************************************)
(******************************************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.

Definition catCategory : category := newCategory
  category
  (functor)
  (fun _ _ _ => compFunctor)
  (fun _ => idFunctor)
  (@compFunctorAssoc)
  (@compFunctorIdentLeft)
  (@compFunctorIdentRight).
