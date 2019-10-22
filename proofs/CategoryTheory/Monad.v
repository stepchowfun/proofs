(********************)
(********************)
(****            ****)
(****   Monads   ****)
(****            ****)
(********************)
(********************)

Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import ProofIrrelevance.

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

Hint Resolve @mAssoc : core.
Hint Resolve @mIdent1 : core.
Hint Rewrite @mIdent1.
Hint Resolve @mIdent2 : core.
Hint Rewrite @mIdent2.

Theorem eqMonad
  {C}
  {F : endofunctor C}
  (Eta : naturalTransformation idFunctor F)
  (Mu : naturalTransformation (compFunctor F F) F)
  (M1 M2 : monad Eta Mu)
: M1 = M2.
Proof.
  destruct M1.
  destruct M2.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve eqMonad : core.
