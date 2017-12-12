(******************************************************************)
(******************************************************************)
(****                                                          ****)
(****   A proof that categories and functors form a category   ****)
(****                                                          ****)
(******************************************************************)
(******************************************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

Hint Resolve proof_irrelevance.

Definition catCategory : category.
Proof.
  refine (
    newCategory
    category
    (fun x y => @functor x y)
    (fun x y z => compFunctor)
    (fun x => idFunctor)
    _ _
  ); intros.
  - destruct f.
    destruct g.
    destruct h.
    unfold compFunctor.
    cbn.
    magic.
  - split;
      intros;
      destruct f;
      unfold compFunctor;
      magic.
Defined.
