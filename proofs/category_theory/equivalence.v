(***************************************)
(***************************************)
(****                               ****)
(****   Equivalence of categories   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.category_theory.functor.
Require Import main.category_theory.natural_transformation.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

Definition equivalence C D
  (F : Functor C D)
  (G : Functor D C)
  (Eta : NaturalTransformation (comp_functor F G) (id_functor C))
  (Mu : NaturalTransformation (id_functor D) (comp_functor G F)) :=
  natural_isomorphism Eta /\ natural_isomorphism Mu.

Definition equivalent C D := exists F G Eta Mu, equivalence C D F G Eta Mu.

Theorem equivalent_refl C : equivalent C C.
Proof.
  unfold equivalent.
  exists (id_functor C).
  exists (id_functor C).
  assert (id_functor C = @comp_functor C C C (id_functor C) (id_functor C)); [
    rewrite comp_functor_ident_left; search |
    idtac
  ].
  exists (
    match H
    in (_ = rhs)
    return NaturalTransformation rhs (id_functor C)
    with
    | eq_refl => (id_natural_transformation (id_functor C))
    end
  ).
  exists (
    match H
    in (_ = rhs)
    return NaturalTransformation (id_functor C) rhs
    with
    | eq_refl => id_natural_transformation (id_functor C)
    end
  ).
  unfold equivalence.
  destruct H.
  split;
    unfold natural_isomorphism;
    clean;
    unfold Isomorphism;
    exists (id x);
    unfold Inverse;
    search.
Qed.

Hint Resolve equivalent_refl : main.
