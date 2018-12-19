(***************************************)
(***************************************)
(****                               ****)
(****   Equivalence of categories   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import Main.Tactics.

Set Universe Polymorphism.

Definition equivalence C D
  (F : functor C D)
  (G : functor D C)
  (Eta : naturalTransformation (compFunctor F G) idFunctor)
  (Mu : naturalTransformation idFunctor (compFunctor G F)) :=
  naturalIsomorphism Eta /\ naturalIsomorphism Mu.

Definition equivalent C D :=
  exists
    (F : functor C D)
    (G : functor D C)
    (Eta : naturalTransformation (compFunctor F G) idFunctor)
    (Mu : naturalTransformation idFunctor (compFunctor G F)),
  equivalence C D F G Eta Mu.

Theorem equivalentRefl C : equivalent C C.
Proof.
  unfold equivalent.
  exists idFunctor.
  exists idFunctor.
  assert (idFunctor = @compFunctor C C C idFunctor idFunctor); [
    rewrite compFunctorIdentLeft; magic |
    idtac
  ].
  exists (
    match H
    in (_ = rhs)
    return naturalTransformation rhs idFunctor
    with
    | eq_refl => idNaturalTransformation
    end
  ).
  exists (
    match H
    in (_ = rhs)
    return naturalTransformation idFunctor rhs
    with
    | eq_refl => idNaturalTransformation
    end
  ).
  unfold equivalence.
  destruct H.
  split; unfold naturalIsomorphism; magic.
Qed.

Hint Resolve equivalentRefl.
