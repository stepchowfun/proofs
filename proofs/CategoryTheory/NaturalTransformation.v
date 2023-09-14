(*************************************)
(*************************************)
(****                             ****)
(****   Natural transformations   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.
#[local] Set Universe Polymorphism.

(* Metavariables for natural transformations: `Eta`, `Mu` *)

Record naturalTransformation {C D} (F G : functor C D) := {
  eta x : arrow (oMap F x) (oMap G x);

  naturality {x y} (f : arrow x y) :
    compose (fMap F f) (eta y) = compose (eta x) (fMap G f);
}.

Arguments eta {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

#[export] Hint Resolve naturality : main.
#[export] Hint Rewrite @naturality : main.

Theorem eqNaturalTransformation
  {C D}
  (F G : functor C D)
  (Eta Mu : naturalTransformation F G)
: eta Eta = eta Mu -> Eta = Mu.
Proof.
  clean.
  assert (
    match H
    in (_ = rhs)
    return
      forall (x y : object C) (f : arrow x y),
      compose (fMap F f) (rhs y) = compose (rhs x) (fMap G f)
    with
    | eq_refl => @naturality C D F G Eta
    end =
    @naturality C D F G Mu
  ).
  - apply proof_irrelevance.
  - destruct Eta.
    destruct Mu.
    search.
Qed.

#[export] Hint Resolve eqNaturalTransformation : main.

Program Definition leftWhisker
  {C D E}
  (F : functor C D)
  {G H : functor D E}
  (Eta : naturalTransformation G H) :
  naturalTransformation (compFunctor F G) (compFunctor F H)
:= {|
  eta x := eta Eta (oMap F x);
|}.

Program Definition rightWhisker
  {C D E}
  {F G : functor C D}
  (Eta : naturalTransformation F G)
  (H : functor D E) :
  naturalTransformation (compFunctor F H) (compFunctor G H)
:= {|
  eta x := fMap H (eta Eta x);
|}.

Program Definition idNaturalTransformation
  {C D}
  (F : functor C D) :
  naturalTransformation F F
:= {|
  eta x := id (oMap F x);
|}.

Program Definition vertCompNaturalTransformation
  {C D}
  {F G H : functor C D}
  (Eta : naturalTransformation F G)
  (Mu : naturalTransformation G H) :
  naturalTransformation F H
:= {|
  eta x := compose (eta Eta x) (eta Mu x);
|}.
Next Obligation.
  clean.
  rewrite cAssoc.
  rewrite <- cAssoc.
  replace (compose (fMap F f) (eta Eta y)) with
    (compose (eta Eta x) (fMap G f)); search.
  replace (compose (eta Mu x) (fMap H f)) with
    (compose (fMap G f) (eta Mu y)); search.
Qed.

Definition horCompNaturalTransformation
  {C D E}
  {F G : functor C D}
  {H K : functor D E}
  (Alpha : naturalTransformation F G)
  (Beta : naturalTransformation H K) :
  naturalTransformation (compFunctor F H) (compFunctor G K)
:= vertCompNaturalTransformation (rightWhisker Alpha H) (leftWhisker G Beta).

Theorem horCompNaturalTransformationAlt
  {C D E}
  {F G : functor C D}
  {H K : functor D E}
  (Alpha : naturalTransformation F G)
  (Beta : naturalTransformation H K)
: horCompNaturalTransformation Alpha Beta =
  vertCompNaturalTransformation (leftWhisker F Beta) (rightWhisker Alpha K).
Proof.
  unfold horCompNaturalTransformation.
  unfold vertCompNaturalTransformation.
  apply eqNaturalTransformation.
  clean.
  apply functional_extensionality_dep.
  search.
Qed.

#[export] Hint Resolve horCompNaturalTransformationAlt : main.

Definition naturalIsomorphism
  {C D} {F G : functor C D}
  (Eta : naturalTransformation F G)
:= forall x, isomorphism (eta Eta x).
