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
    eta (vertCompNaturalTransformation Mu (leftWhisker Mu F)) =
    eta (vertCompNaturalTransformation Mu (rightWhisker F Mu));
  mIdent1 :
    eta (vertCompNaturalTransformation Mu (leftWhisker Eta F)) =
    eta idNaturalTransformation;
  mIdent2 :
    eta (vertCompNaturalTransformation Mu (rightWhisker F Eta)) =
    eta idNaturalTransformation;
}.

Hint Resolve @mAssoc.
Hint Resolve @mIdent1.
Hint Rewrite @mIdent1.
Hint Resolve @mIdent2.
Hint Rewrite @mIdent2.
