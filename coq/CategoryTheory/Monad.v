(********************)
(********************)
(****            ****)
(****   Monads   ****)
(****            ****)
(********************)
(********************)

Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.

Set Universe Polymorphism.

(* Metavariable for monads: M *)

Record monad
  {C}
  {F : endofunctor C}
  (Eta : naturalTransformation idFunctor F)
  (Mu : naturalTransformation (compFunctor F F) F) :=
newMonad {
  mAssoc :
    eta (compNaturalTransformation Mu (leftWhisker Mu F)) =
    eta (compNaturalTransformation Mu (rightWhisker F Mu));
  mIdent1 :
    eta (compNaturalTransformation Mu (leftWhisker Eta F)) =
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
