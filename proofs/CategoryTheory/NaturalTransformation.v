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

#[local] Set Universe Polymorphism.

(* Metavariables for natural transformations: Eta, Mu *)

Record naturalTransformation {C D} (F G : functor C D) :=
newNaturalTransformation {
  eta x : arrow (oMap F x) (oMap G x);

  naturality {x y} (f : arrow x y) :
    compose (eta y) (fMap F f) = compose (fMap G f) (eta x);
}.

Arguments newNaturalTransformation {_} {_}.
Arguments eta {_} {_} {_} {_} _.
Arguments naturality {_} {_} {_} {_} _ {_} {_}.

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
      compose (rhs y) (fMap F f) = compose (fMap G f) (rhs x)
    with
    | eq_refl => @naturality C D F G Eta
    end =
    @naturality C D F G Mu
  ).
  - apply proof_irrelevance.
  - destruct Eta.
    destruct Mu.
    magic.
Qed.

#[export] Hint Resolve eqNaturalTransformation : main.

#[local] Theorem rightWhiskerNaturality
  {C D E}
  {F G : functor C D}
  {H : functor D E}
  {Eta : naturalTransformation F G}
  (x y : object C) (f : arrow x y)
: compose (fMap H (eta Eta y)) (fMap (compFunctor H F) f) =
  compose (fMap (compFunctor H G) f)  (fMap H (eta Eta x)).
Proof.
  magic.
Qed.

Definition rightWhisker
  {C D E}
  {F G : functor C D}
  (H : functor D E)
  (Eta : naturalTransformation F G) :
  naturalTransformation (compFunctor H F) (compFunctor H G)
:= newNaturalTransformation (compFunctor H F) (compFunctor H G)
  (fun x => fMap H (eta Eta x))
  rightWhiskerNaturality.

#[local] Theorem leftWhiskerNaturality
  {C D E}
  {F G : functor D E}
  {Eta : naturalTransformation F G}
  {H : functor C D}
  (x y : object C)
  (f : arrow x y)
: compose (eta Eta (oMap H y)) (fMap (compFunctor F H) f) =
  compose (fMap (compFunctor G H) f) (eta Eta (oMap H x)).
Proof.
  magic.
Qed.

Definition leftWhisker
  {C D E}
  {F G : functor D E}
  (Eta : naturalTransformation F G)
  (H : functor C D) :
  naturalTransformation (compFunctor F H) (compFunctor G H)
:= newNaturalTransformation (compFunctor F H) (compFunctor G H)
  (fun x => eta Eta (oMap H x))
  leftWhiskerNaturality.

#[local] Theorem idNaturality
  {C D}
  {F : functor C D}
  (x y : object C)
  (f : arrow x y)
: compose id (fMap F f) = compose (fMap F f) id.
Proof.
  magic.
Qed.

Definition idNaturalTransformation
  {C D}
  {F : functor C D} :
  naturalTransformation F F
:= newNaturalTransformation F F (fun x => id) idNaturality.

#[local] Theorem vertCompNaturality
  {C D}
  {F G H : functor C D}
  {Eta : naturalTransformation G H}
  {Mu : naturalTransformation F G}
  (x y : object C) (f : arrow x y)
: compose (compose (eta Eta y) (eta Mu y)) (fMap F f) =
  compose (fMap H f) (compose (eta Eta x) (eta Mu x)).
Proof.
  rewrite cAssoc.
  rewrite <- cAssoc.
  replace (compose (eta Mu y) (fMap F f)) with
    (compose (fMap G f) (eta Mu x)); magic.
  replace (compose (fMap H f) (eta Eta x)) with
    (compose (eta Eta y) (fMap G f)); magic.
Qed.

Definition vertCompNaturalTransformation
  {C D}
  {F G H : functor C D}
  (Eta : naturalTransformation G H)
  (Mu : naturalTransformation F G) :
  naturalTransformation F H
:= newNaturalTransformation F H
  (fun x => compose (eta Eta x) (eta Mu x))
  vertCompNaturality.

Definition horCompNaturalTransformation
  {C D E}
  {F G : functor C D}
  {K H : functor D E}
  (Beta : naturalTransformation H K)
  (Alpha : naturalTransformation F G) :
  naturalTransformation (compFunctor H F) (compFunctor K G)
:= vertCompNaturalTransformation (leftWhisker Beta G) (rightWhisker H Alpha).

Theorem horCompNaturalTransformationAlt
  {C D E}
  {F G : functor C D}
  {K H : functor D E}
  (Beta : naturalTransformation H K)
  (Alpha : naturalTransformation F G)
: horCompNaturalTransformation Beta Alpha =
  vertCompNaturalTransformation (rightWhisker K Alpha) (leftWhisker Beta F).
Proof.
  unfold horCompNaturalTransformation.
  unfold vertCompNaturalTransformation.
  apply eqNaturalTransformation.
  clean.
  apply functional_extensionality_dep.
  magic.
Qed.

#[export] Hint Resolve horCompNaturalTransformationAlt : main.

Definition naturalIsomorphism
  {C D} {F G : functor C D}
  (Eta : naturalTransformation F G) :=
  forall x, isomorphism (eta Eta x).
