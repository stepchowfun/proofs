(*************************************)
(*************************************)
(****                             ****)
(****   Natural transformations   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

(* Metavariables for natural transformations: Eta, Mu *)

Record naturalTransformation
    {C D : category}
    {F G : @functor C D} :=
    newNaturalTransformation {
  eta : forall x, arrow D (oMap F x) (oMap G x);

  naturality :
    forall x y (f : arrow C x y),
    compose D (eta y) (fMap F f) = compose D (fMap G f) (eta x);
}.

Hint Resolve @naturality.
Hint Rewrite @naturality.

Definition idNaturalTransformation
    {C D : category}
    {F : @functor C D} :
    @naturalTransformation C D F F.
Proof.
  refine (
    newNaturalTransformation C D F F
    (fun x => id D)
    _
  ); magic.
Defined.

Definition compNaturalTransformation
    {C D : category}
    {F G H : @functor C D}
    (Eta : @naturalTransformation C D G H)
    (Mu : @naturalTransformation C D F G) :
    @naturalTransformation C D F H.
Proof.
  refine (
    newNaturalTransformation C D F H
    (fun x => compose D (eta Eta x) (eta Mu x))
    _
  ).
  intros.
  replace (compose D (compose D (eta Eta y) (eta Mu y)) (fMap F f)) with
    (compose D (eta Eta y) (compose D (eta Mu y) (fMap F f))); magic.
Defined.

Definition rightWhisker
    {C D E : category}
    {F G : @functor C D}
    (H : @functor D E)
    (Eta : @naturalTransformation C D F G) :
    @naturalTransformation C E (compFunctor H F) (compFunctor H G).
Proof.
  refine (
    newNaturalTransformation C E (compFunctor H F) (compFunctor H G)
    (fun x => fMap H (eta Eta x))
    _
  ); magic.
Defined.

Definition leftWhisker
    {C D E : category}
    {F G : @functor D E}
    (H : @functor C D)
    (Eta : @naturalTransformation D E F G) :
    @naturalTransformation C E (compFunctor F H) (compFunctor G H).
Proof.
  refine (
    newNaturalTransformation C E (compFunctor F H) (compFunctor G H)
    (fun x => eta Eta (oMap H x))
    _
  ); magic.
Defined.
