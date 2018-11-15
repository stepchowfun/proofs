(******************************************************************)
(******************************************************************)
(****                                                          ****)
(****   A proof that categories and functors form a category   ****)
(****                                                          ****)
(******************************************************************)
(******************************************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.
Require Import ProofIrrelevance.

Section ProofIrrelevance.
  Hint Resolve proof_irrelevance.

  Definition catCategory : category.
  Proof.
    refine (
      newCategory
      category
      (fun x y => @functor x y)
      (fun x y z => compFunctor)
      (fun x => idFunctor)
      _ _ _
    ); unfold compFunctor; destruct f; magic.
  Defined.
End ProofIrrelevance.
