(*******************************************)
(*******************************************)
(****                                   ****)
(****   A proof that maybe is a monad   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import FunctionalExtensionality.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Examples.Set.
Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.Monad.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import Main.Tactics.

(* A maybe is a wrapper for value that might be missing. *)

Inductive maybe {x} : Type :=
| nothing : @maybe x
| just : x -> @maybe x.

(* Here's a proof that maybe is a functor. *)

Let maybeFIdent (x : object setCategory) :
  (
    fun e : maybe =>
      match e with
      | nothing => nothing
      | just e0 => just (@id setCategory x e0)
      end
  ) = id setCategory.
Proof.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Let maybeFComp
  (x y z : object setCategory)
  (f : arrow setCategory x y)
  (g : arrow setCategory y z)
: compose setCategory
    (
      fun e : maybe =>
        match e with
        | nothing => nothing
        | just e0 => just (g e0)
        end
    )
    (
      fun e : maybe =>
        match e with
        | nothing => nothing
        | just e0 => just (f e0)
        end
    ) =
  (
    fun e : maybe =>
      match e with
      | nothing => nothing
      | just e0 => just (compose setCategory g f e0)
      end
  ).
Proof.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Definition maybeFunctor : @functor setCategory setCategory := newFunctor
  setCategory
  setCategory
  (@maybe)
  (fun _ _ f e =>
    match e with
    | nothing => nothing
    | just e => just (f e)
    end
  )
  maybeFIdent
  maybeFComp.

(* This is the "return" natural transformation for maybe. *)

Let maybeEtaNaturality (x y : object setCategory) (f : arrow setCategory x y) :
  compose setCategory just (fMap idFunctor f) =
  compose setCategory (fMap maybeFunctor f) just.
Proof.
  magic.
Qed.

Definition maybeEta :
  @naturalTransformation setCategory setCategory idFunctor maybeFunctor
:= newNaturalTransformation
  setCategory
  setCategory
  idFunctor
  maybeFunctor
  (@just)
  maybeEtaNaturality.

(* This is the "join" natural transformation for maybe. *)

Let maybeMuNaturality (x y : object setCategory) (f : arrow setCategory x y) :
  compose
    setCategory
    (
      fun e1 : oMap (compFunctor maybeFunctor maybeFunctor) y =>
        match e1 with
        | nothing => nothing
        | just e2 => e2
        end
    )
    (fMap (compFunctor maybeFunctor maybeFunctor) f) =
  compose
    setCategory
    (fMap maybeFunctor f)
    (
      fun e1 : oMap (compFunctor maybeFunctor maybeFunctor) x =>
        match e1 with
        | nothing => nothing
        | just e2 => e2
        end
    ).
Proof.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Definition maybeMu : @naturalTransformation
  setCategory
  setCategory
  (compFunctor maybeFunctor maybeFunctor)
  maybeFunctor
:= newNaturalTransformation
  setCategory
  setCategory
  (compFunctor maybeFunctor maybeFunctor)
  maybeFunctor
  (
    fun x e1 =>
      match e1 with
      | nothing => nothing
      | just e2 => e2
      end
  )
  maybeMuNaturality.

(* Now we can prove that maybe is a monad. *)

Let maybeMAssoc :
  eta (compNaturalTransformation maybeMu (leftWhisker maybeMu maybeFunctor)) =
  eta (compNaturalTransformation maybeMu (rightWhisker maybeFunctor maybeMu)).
Proof.
  clean.
  apply functional_extensionality_dep.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Let maybeMIdent1 :
  eta (compNaturalTransformation maybeMu (leftWhisker maybeEta maybeFunctor)) =
  eta idNaturalTransformation.
Proof.
  magic.
Qed.

Let maybeMIdent2 :
  eta
    (compNaturalTransformation maybeMu (rightWhisker maybeFunctor maybeEta)) =
  eta idNaturalTransformation.
Proof.
  clean.
  apply functional_extensionality_dep.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Definition maybeMonad : monad maybeEta maybeMu := newMonad
  setCategory
  maybeFunctor
  maybeEta
  maybeMu
  maybeMAssoc
  maybeMIdent1
  maybeMIdent2.
