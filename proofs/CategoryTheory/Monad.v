(********************)
(********************)
(****            ****)
(****   Monads   ****)
(****            ****)
(********************)
(********************)

Require Import Coq.Logic.ProofIrrelevance.
Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.NaturalTransformation.

#[local] Set Universe Polymorphism.

(* Metavariable for monads: `M` *)

Record monad
  {C}
  {F : endofunctor C}
  (Eta : naturalTransformation (idFunctor C) F)
  (Mu : naturalTransformation (compFunctor F F) F)
:= {
  mAssoc :
    eta (vertCompNaturalTransformation (leftWhisker F Mu) Mu) =
    eta (vertCompNaturalTransformation (rightWhisker Mu F) Mu);
  mIdent1 :
    eta (vertCompNaturalTransformation (leftWhisker F Eta) Mu) =
    eta (idNaturalTransformation F);
  mIdent2 :
    eta (vertCompNaturalTransformation (rightWhisker Eta F) Mu) =
    eta (idNaturalTransformation F);
}.

Arguments mAssoc {_ _ _ _} _.
Arguments mIdent1 {_ _ _ _} _.
Arguments mIdent2 {_ _ _ _} _.

#[export] Hint Resolve mAssoc : main.
#[export] Hint Resolve mIdent1 : main.
#[export] Hint Rewrite @mIdent1 : main.
#[export] Hint Resolve mIdent2 : main.
#[export] Hint Rewrite @mIdent2 : main.

Theorem eqMonad
  {C}
  {F : endofunctor C}
  (Eta : naturalTransformation (idFunctor C) F)
  (Mu : naturalTransformation (compFunctor F F) F)
  (M1 M2 : monad Eta Mu)
: M1 = M2.
Proof.
  destruct M1.
  destruct M2.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve eqMonad : main.
