(********************)
(********************)
(****            ****)
(****   Monads   ****)
(****            ****)
(********************)
(********************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariable for monads: M *)

Record monad
  {C : category}
  {F : @functor C C}
  (Eta : @naturalTransformation C C idFunctor F)
  (Mu : @naturalTransformation C C (compFunctor F F) F) :=
newMonad {
  mAssoc :
    eta (compNaturalTransformation Mu (leftWhisker F Mu)) =
    eta (compNaturalTransformation Mu (rightWhisker F Mu));
  mIdent1 :
    eta (compNaturalTransformation Mu (leftWhisker F Eta)) =
    eta idNaturalTransformation;
  mIdent2 :
    eta (compNaturalTransformation Mu (rightWhisker F Eta)) =
    eta idNaturalTransformation;
}.

Hint Resolve @mAssoc.
Hint Resolve @mIdent1.
Hint Rewrite @mIdent1.
Hint Resolve @mIdent2.
Hint Rewrite @mIdent2.
