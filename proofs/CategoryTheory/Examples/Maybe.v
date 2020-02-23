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

Inductive maybe x : Type :=
| nothing : maybe x
| just : x -> maybe x.

Arguments nothing {_}.
Arguments just {_}.

(* Here's a proof that maybe is a functor. *)

Local Theorem maybeFIdent (x : object setCategory) :
  (
    fun e : maybe x =>
      match e with
      | nothing => nothing
      | just e0 => just (@id setCategory x e0)
      end
  ) = @id setCategory (maybe x).
Proof.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Local Theorem maybeFComp
  (x y z : object setCategory)
  (f : arrow x y)
  (g : arrow y z)
: @compose setCategory _ _ _
    (
      fun e : maybe y =>
        match e with
        | nothing => nothing
        | just e0 => just (g e0)
        end
    )
    (
      fun e : maybe x =>
        match e with
        | nothing => nothing
        | just e0 => just (f e0)
        end
    ) =
  (
    fun e : maybe x =>
      match e with
      | nothing => nothing
      | just e0 => just (compose g f e0)
      end
  ).
Proof.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Definition maybeFunctor : functor setCategory setCategory := newFunctor
  setCategory
  setCategory
  maybe
  (fun _ _ f e =>
    match e with
    | nothing => nothing
    | just e => just (f e)
    end
  )
  maybeFIdent
  maybeFComp.

(* This is the "return" natural transformation for maybe. *)

Local Theorem maybeEtaNaturality (x y : object setCategory) (f : arrow x y) :
  @compose setCategory _ _ _ just (fMap idFunctor f) =
  @compose setCategory _ _ _ (fMap maybeFunctor f) just.
Proof.
  magic.
Qed.

Definition maybeEta : naturalTransformation idFunctor maybeFunctor :=
  newNaturalTransformation
    idFunctor
    maybeFunctor
    (@just)
    maybeEtaNaturality.

(* This is the "join" natural transformation for maybe. *)

Local Theorem maybeMuNaturality (x y : object setCategory) (f : arrow x y) :
  @compose
    setCategory _ _ _
    (
      fun e1 : oMap (compFunctor maybeFunctor maybeFunctor) y =>
        match e1 with
        | nothing => nothing
        | just e2 => e2
        end
    )
    (fMap (compFunctor maybeFunctor maybeFunctor) f) =
  compose
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

Definition maybeMu :
  naturalTransformation (compFunctor maybeFunctor maybeFunctor) maybeFunctor
:= newNaturalTransformation
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

Local Theorem maybeMAssoc :
  eta (
    vertCompNaturalTransformation maybeMu (leftWhisker maybeMu maybeFunctor)
  ) = eta (
    vertCompNaturalTransformation maybeMu (rightWhisker maybeFunctor maybeMu)
  ).
Proof.
  clean.
  apply functional_extensionality_dep.
  clean.
  apply functional_extensionality.
  destruct x0; magic.
Qed.

Local Theorem maybeMIdent1 :
  eta (
    vertCompNaturalTransformation maybeMu (leftWhisker maybeEta maybeFunctor)
  ) = eta idNaturalTransformation.
Proof.
  magic.
Qed.

Local Theorem maybeMIdent2 :
  eta (
    vertCompNaturalTransformation maybeMu (rightWhisker maybeFunctor maybeEta)
  ) = eta idNaturalTransformation.
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
