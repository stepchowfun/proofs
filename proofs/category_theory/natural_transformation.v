(*************************************)
(*************************************)
(****                             ****)
(****   Natural transformations   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.category_theory.functor.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

(* Metavariables for natural transformations: `Eta`, `Mu` *)

Record NaturalTransformation [C D] (F G : Functor C D) := {
  eta x : Arrow (o_map F x) (o_map G x);

  naturality [x y] (f : Arrow x y) :
    compose (f_map F f) (eta y) = compose (eta x) (f_map G f);
}.

Arguments eta [_ _ _ _] _ _.
Arguments naturality [_ _ _ _] _ [_ _] _.

Hint Resolve naturality : main.
Hint Rewrite @naturality : main.

Theorem eq_natural_transformation
  [C D]
  (F G : Functor C D)
  (Eta Mu : NaturalTransformation F G)
: eta Eta = eta Mu -> Eta = Mu.
Proof.
  clean.
  assert (
    match H
    in (_ = rhs)
    return
      forall (x y : Object C) (f : Arrow x y),
      compose (f_map F f) (rhs y) = compose (rhs x) (f_map G f)
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

Hint Resolve eq_natural_transformation : main.

Program Definition left_whisker
  [C D E]
  (F : Functor C D)
  [G H : Functor D E]
  (Eta : NaturalTransformation G H) :
  NaturalTransformation (comp_functor F G) (comp_functor F H)
:= {|
  eta x := eta Eta (o_map F x);
|}.

Program Definition right_whisker
  [C D E]
  [F G : Functor C D]
  (Eta : NaturalTransformation F G)
  (H : Functor D E) :
  NaturalTransformation (comp_functor F H) (comp_functor G H)
:= {|
  eta x := f_map H (eta Eta x);
|}.

Program Definition id_natural_transformation
  [C D]
  (F : Functor C D) :
  NaturalTransformation F F
:= {|
  eta x := id (o_map F x);
|}.

Program Definition vert_comp_natural_transformation
  [C D]
  [F G H : Functor C D]
  (Eta : NaturalTransformation F G)
  (Mu : NaturalTransformation G H) :
  NaturalTransformation F H
:= {|
  eta x := compose (eta Eta x) (eta Mu x);
|}.
Next Obligation.
  clean.
  rewrite c_assoc.
  rewrite <- c_assoc.
  replace (compose (f_map F f) (eta Eta y)) with
    (compose (eta Eta x) (f_map G f)); search.
  replace (compose (eta Mu x) (f_map H f)) with
    (compose (f_map G f) (eta Mu y)); search.
Qed.

Definition hor_comp_natural_transformation
  [C D E]
  [F G : Functor C D]
  [H K : Functor D E]
  (Alpha : NaturalTransformation F G)
  (Beta : NaturalTransformation H K) :
  NaturalTransformation (comp_functor F H) (comp_functor G K)
:=
  vert_comp_natural_transformation
    (right_whisker Alpha H)
    (left_whisker G Beta).

Theorem hor_comp_natural_transformation_alt
  [C D E]
  [F G : Functor C D]
  [H K : Functor D E]
  (Alpha : NaturalTransformation F G)
  (Beta : NaturalTransformation H K)
: hor_comp_natural_transformation Alpha Beta =
  vert_comp_natural_transformation
    (left_whisker F Beta)
    (right_whisker Alpha K).
Proof.
  unfold hor_comp_natural_transformation.
  unfold vert_comp_natural_transformation.
  apply eq_natural_transformation.
  clean.
  apply functional_extensionality_dep.
  search.
Qed.

Hint Resolve hor_comp_natural_transformation_alt : main.

Definition natural_isomorphism
  [C D] [F G : Functor C D]
  (Eta : NaturalTransformation F G)
:= forall x, Isomorphism (eta Eta x).
