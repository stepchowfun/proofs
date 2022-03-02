(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   The category of categories and functors   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

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
