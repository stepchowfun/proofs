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
    f_equal.
    apply proof_irrelevance.
    do 5 (apply functional_extensionality_dep; intros).
    apply proof_irrelevance.
  - split;
      intros;
      destruct f;
      unfold compFunctor;
      cbn;
      f_equal;
      apply proof_irrelevance.
Defined.
