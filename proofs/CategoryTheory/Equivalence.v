(***************************************)
(***************************************)
(****                               ****)
(****   Equivalence of categories   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import Main.Tactics.

#[local] Set Universe Polymorphism.

Definition equivalence C D
  (F : functor C D)
  (G : functor D C)
  (Eta : naturalTransformation (compFunctor F G) (idFunctor C))
  (Mu : naturalTransformation (idFunctor D) (compFunctor G F)) :=
  naturalIsomorphism Eta /\ naturalIsomorphism Mu.

Definition equivalent C D := exists F G Eta Mu, equivalence C D F G Eta Mu.

Theorem equivalentRefl C : equivalent C C.
Proof.
  unfold equivalent.
  exists (idFunctor C).
  exists (idFunctor C).
  assert (idFunctor C = @compFunctor C C C (idFunctor C) (idFunctor C)); [
    rewrite compFunctorIdentLeft; search |
    idtac
  ].
  exists (
    match H
    in (_ = rhs)
    return naturalTransformation rhs (idFunctor C)
    with
    | eq_refl => (idNaturalTransformation (idFunctor C))
    end
  ).
  exists (
    match H
    in (_ = rhs)
    return naturalTransformation (idFunctor C) rhs
    with
    | eq_refl => idNaturalTransformation (idFunctor C)
    end
  ).
  unfold equivalence.
  destruct H.
  split;
    unfold naturalIsomorphism;
    clean;
    unfold isomorphism;
    exists (id x);
    unfold inverse;
    search.
Qed.

#[export] Hint Resolve equivalentRefl : main.
