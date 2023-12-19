(*******************************************)
(*******************************************)
(****                                   ****)
(****   A proof that maybe is a monad   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import main.category_theory.examples.set.
Require Import main.category_theory.functor.
Require Import main.category_theory.monad.
Require Import main.category_theory.natural_transformation.
Require Import main.tactics.

(* A `Maybe` is a wrapper for value that might be missing. *)

Inductive Maybe T : Type :=
| nothing : Maybe T
| just : T -> Maybe T.

Arguments just [_].

(* `Maybe` is a functor. *)

Program Definition maybe_functor : Functor set_category set_category := {|
  o_map o := Maybe o;
  f_map _ _ f := fun e =>
    match e with
    | nothing _ => nothing _
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

(* This is the "return" natural transformation for `Maybe`. *)

Program Definition maybe_eta :
  NaturalTransformation (id_functor set_category) maybe_functor
:= {|
  eta x := @just x;
|}.

(* This is the "join" natural transformation for `Maybe`. *)

Program Definition maybe_mu :
  NaturalTransformation
    (comp_functor maybe_functor maybe_functor)
    maybe_functor
:= {|
  eta x :=
    fun e1 =>
      match e1 with
      | nothing _ => nothing _
      | just e2 => e2
      end
|}.
Next Obligation.
  clean.
  apply functional_extensionality.
  destruct x0; search.
Qed.

(* Now we can show that `Maybe` is a monad. *)

Program Definition maybe_monad : Monad maybe_eta maybe_mu := {|
  m_assoc := _;
  m_ident1 := _;
  m_ident2 := _;
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
