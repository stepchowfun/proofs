(*******************************************)
(*******************************************)
(****                                   ****)
(****   A proof that maybe is a monad   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Main.CategoryTheory.Examples.Set.
Require Import Main.CategoryTheory.Functor.
Require Import Main.CategoryTheory.Monad.
Require Import Main.CategoryTheory.NaturalTransformation.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.

(* A `maybe` is a wrapper for value that might be missing. *)

Inductive maybe x : Type :=
| nothing : maybe x
| just : x -> maybe x.

Arguments nothing {_}.
Arguments just {_}.

(* `maybe` is a functor. *)

Program Definition maybeFunctor : functor setCategory setCategory := {|
  oMap o := maybe o;
  fMap _ _ f := fun e =>
    match e with
    | nothing => nothing
    | just e => just (f e)
    end;
|}.
Next Obligation.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.
Next Obligation.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.

(* This is the "return" natural transformation for `maybe`. *)

Program Definition maybeEta :
  naturalTransformation (idFunctor setCategory) maybeFunctor
:= {|
  eta x := @just x;
|}.

(* This is the "join" natural transformation for `maybe`. *)

Program Definition maybeMu :
  naturalTransformation (compFunctor maybeFunctor maybeFunctor) maybeFunctor
:= {|
  eta x :=
    fun e1 =>
      match e1 with
      | nothing => nothing
      | just e2 => e2
      end
|}.
Next Obligation.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.

(* Now we can show that `maybe` is a monad. *)

Program Definition maybeMonad : monad maybeEta maybeMu := {|
  mAssoc := _;
  mIdent1 := _;
  mIdent2 := _;
|}.
Next Obligation.
  clean.
  apply functional_extensionality_dep.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.
Next Obligation.
  clean.
  apply functional_extensionality_dep.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.
