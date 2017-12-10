(********************************************)
(********************************************)
(****                                    ****)
(****   A proof that Maybe is a Monad.   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Main.CategoryTheory.Definitions.
Require Import Main.CategoryTheory.Set.

(***********************)
(* Maybe is a Functor. *)
(***********************)

Inductive Maybe {X : Set} : Set :=
| Nothing : @Maybe X
| Just : X -> @Maybe X.

Module MaybeFunctor <: Functor SetCategory SetCategory.
  Definition oMap (X : SetCategory.Object) := @Maybe X.
  Definition fMap {X Y} (f : SetCategory.Arrow X Y) x :=
    match x with
    | Nothing => Nothing
    | Just x => Just (f x)
    end.

  Theorem ident :
    forall X,
    fMap (@SetCategory.id X) = @SetCategory.id (oMap X).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    unfold fMap.
    destruct x; auto.
  Qed.

  Theorem comp :
    forall X Y Z (f : SetCategory.Arrow X Y) (g : SetCategory.Arrow Y Z),
    fMap (SetCategory.compose g f) = SetCategory.compose (fMap g) (fMap f).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    destruct x; auto.
  Qed.
End MaybeFunctor.

(*************************************************************)
(* The return function for Maybe is a NaturalTransformation. *)
(*************************************************************)

Module SetIdentityFunctor := IdentityFunctor SetCategory.

Module MaybeEtaNaturalTransformation <: NaturalTransformation
    SetCategory
    SetCategory
    SetIdentityFunctor
    MaybeFunctor.
  Definition eta X x := @Just X x.

  Theorem naturality :
    forall X Y (f : SetCategory.Arrow X Y),
    SetCategory.compose (eta Y) (SetIdentityFunctor.fMap f) =
      SetCategory.compose (MaybeFunctor.fMap f) (eta X).
  Proof.
    intros.
    apply functional_extensionality.
    auto.
  Qed.
End MaybeEtaNaturalTransformation.

(***********************************************************)
(* The bind function for Maybe is a NaturalTransformation. *)
(***********************************************************)

Module SquareMaybeFunctor := FunctorComposition
  SetCategory
  SetCategory
  SetCategory
  MaybeFunctor
  MaybeFunctor.

Module MaybeMuNaturalTransformation <: NaturalTransformation
    SetCategory
    SetCategory
    SquareMaybeFunctor
    MaybeFunctor.
  Definition eta X (x : @Maybe (@Maybe X)) :=
    match x with
    | Nothing => Nothing
    | Just y => y
    end.

  Theorem naturality :
    forall X Y (f : SetCategory.Arrow X Y),
    SetCategory.compose (eta Y) (SquareMaybeFunctor.fMap f) =
      SetCategory.compose (MaybeFunctor.fMap f) (eta X).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    unfold SetCategory.compose.
    unfold SquareMaybeFunctor.fMap.
    unfold MaybeFunctor.fMap.
    unfold eta.
    destruct x; auto.
  Qed.
End MaybeMuNaturalTransformation.

(*********************)
(* Maybe is a Monad. *)
(*********************)

Module MaybeMonad'' := Monad'' SetCategory MaybeFunctor.
Module MaybeMonad' := MaybeMonad''.Monad'
  MaybeEtaNaturalTransformation
  MaybeMuNaturalTransformation.

Module MaybeMonad <: MaybeMonad'.Monad.
  Import MaybeMonad'.

  Theorem assoc : MuAfterTMu.eta = MuAfterMuT.eta.
  Proof.
    unfold MuAfterTMu.eta.
    unfold MuAfterMuT.eta.
    apply functional_extensionality_dep.
    intros.
    unfold SetCategory.compose.
    apply functional_extensionality.
    intros.
    unfold TMu.eta.
    unfold MuT.eta.
    unfold MaybeMuNaturalTransformation.eta.
    destruct x0; unfold MaybeFunctor.fMap; auto.
  Qed.

  Theorem ident1 : MuAfterTEta.eta = IdT.eta.
  Proof.
    apply functional_extensionality_dep.
    intros.
    unfold MuAfterTEta.eta.
    unfold IdT.eta.
    unfold SetCategory.compose.
    apply functional_extensionality.
    intros.
    unfold SetCategory.id.
    unfold TEta.eta.
    unfold MaybeFunctor.oMap.
    unfold MaybeEtaNaturalTransformation.eta.
    unfold MaybeMuNaturalTransformation.eta.
    auto.
  Qed.

  Theorem ident2 : MuAfterEtaT.eta = IdT.eta.
  Proof.
    apply functional_extensionality_dep.
    intros.
    unfold MuAfterEtaT.eta.
    unfold IdT.eta.
    unfold SetCategory.compose.
    apply functional_extensionality.
    intros.
    unfold SetCategory.id.
    unfold EtaT.eta.
    unfold MaybeEtaNaturalTransformation.eta.
    unfold MaybeFunctor.fMap.
    unfold MaybeMuNaturalTransformation.eta.
    destruct x0; auto.
  Qed.
End MaybeMonad.
