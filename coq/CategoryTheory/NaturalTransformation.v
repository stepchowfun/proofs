(*************************************)
(*************************************)
(****                             ****)
(****   Natural transformations   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Functor.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariables for natural transformations: Eta, Mu *)

Record naturalTransformation
  {C D : category}
  {F G : @functor C D} :=
newNaturalTransformation {
  eta x : arrow D (oMap F x) (oMap G x);

  naturality x y (f : arrow C x y) :
    compose D (eta y) (fMap F f) = compose D (fMap G f) (eta x);
}.

Hint Resolve @naturality.
Hint Rewrite @naturality.

Let idNaturality
  {C D : category}
  {F : @functor C D}
  (x y : object C)
  (f : arrow C x y)
: compose D (id D) (fMap F f) = compose D (fMap F f) (id D).
Proof.
  magic.
Qed.

Definition idNaturalTransformation
  {C D : category}
  {F : @functor C D} :
  @naturalTransformation C D F F
:= newNaturalTransformation C D F F
  (fun x => id D)
  idNaturality.

Let compNaturality
  {C D : category}
  {F G H : @functor C D}
  {Eta : @naturalTransformation C D G H}
  {Mu : @naturalTransformation C D F G}
  (x y : object C) (f : arrow C x y)
: compose D (compose D (eta Eta y) (eta Mu y)) (fMap F f) =
  compose D (fMap H f) (compose D (eta Eta x) (eta Mu x)).
Proof.
  rewrite cAssoc.
  rewrite <- cAssoc.
  replace (compose D (eta Mu y) (fMap F f)) with
    (compose D (fMap G f) (eta Mu x)); magic.
  replace (compose D (fMap H f) (eta Eta x)) with
    (compose D (eta Eta y) (fMap G f)); magic.
Qed.

Definition compNaturalTransformation
  {C D : category}
  {F G H : @functor C D}
  (Eta : @naturalTransformation C D G H)
  (Mu : @naturalTransformation C D F G) :
  @naturalTransformation C D F H
:= newNaturalTransformation C D F H
    (fun x => compose D (eta Eta x) (eta Mu x))
    compNaturality.

Let rightWhiskerNaturality
  {C D E : category}
  {F G : @functor C D}
  {H : @functor D E}
  {Eta : @naturalTransformation C D F G}
  (x y : object C) (f : arrow C x y)
: compose E (fMap H (eta Eta y)) (fMap (compFunctor H F) f) =
  compose E (fMap (compFunctor H G) f)  (fMap H (eta Eta x)).
Proof.
  magic.
Qed.

Definition rightWhisker
  {C D E : category}
  {F G : @functor C D}
  (H : @functor D E)
  (Eta : @naturalTransformation C D F G) :
  @naturalTransformation C E (compFunctor H F) (compFunctor H G)
:= newNaturalTransformation C E (compFunctor H F) (compFunctor H G)
  (fun x => fMap H (eta Eta x))
  rightWhiskerNaturality.

Let leftWhiskerNaturality
  {C D E : category}
  {F G : @functor D E}
  {Eta : @naturalTransformation D E F G}
  {H : @functor C D}
  (x y : object C)
  (f : arrow C x y)
: compose E (eta Eta (oMap H y))
    (fMap (compFunctor F H) f) =
  compose E (fMap (compFunctor G H) f)
    (eta Eta (oMap H x)).
Proof.
  magic.
Qed.

Definition leftWhisker
  {C D E : category}
  {F G : @functor D E}
  (Eta : @naturalTransformation D E F G)
  (H : @functor C D) :
  @naturalTransformation C E (compFunctor F H) (compFunctor G H)
:= newNaturalTransformation C E (compFunctor F H) (compFunctor G H)
    (fun x => eta Eta (oMap H x))
    leftWhiskerNaturality.

Definition naturalIsomorphism
  {C D F G}
  (Eta : @naturalTransformation C D F G) :=
  forall x, isomorphism (eta Eta x).
