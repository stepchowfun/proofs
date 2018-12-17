(***************************************)
(***************************************)
(****                               ****)
(****   Equivalence of categories   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.

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
