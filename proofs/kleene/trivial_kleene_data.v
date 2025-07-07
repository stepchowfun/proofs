(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   The simplest possible pointed directed-complete partial order   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

Require Import main.kleene.kleene_data.
Require Import main.kleene.kleene_theorems.
Require Import main.tactics.

Module TrivialKleeneData <: KleeneData.
  Definition T := unit.

  Hint Unfold T : main.

  Definition Leq (x y : T) := True.

  Hint Unfold Leq : main.

  Theorem reflexivity : forall x, Leq x x.
  Proof.
    search.
  Qed.

  #[local] Hint Resolve reflexivity : main.

  Theorem transitivity : forall x y z, Leq x y -> Leq y z -> Leq x z.
  Proof.
    search.
  Qed.

  #[local] Hint Resolve transitivity : main.

  Theorem antisymmetry : forall x y, Leq x y -> Leq y x -> x = y.
  Proof.
    search.
  Qed.

  #[local] Hint Resolve antisymmetry : main.

  (* Rocq requires that we copy this verbatim from `ContextGraph`. *)
  Definition Supremum P x1 :=
    (forall x2, P x2 -> Leq x2 x1) /\
    forall x3, (forall x2, P x2 -> Leq x2 x3) -> Leq x1 x3.

  Hint Unfold Supremum : main.

  (* Rocq requires that we copy this verbatim from `ContextGraph`. *)
  Definition Directed P :=
    (exists x1, P x1) /\
    forall x1 x2, P x1 -> P x2 -> exists x3, Leq x1 x3 /\ Leq x2 x3 /\ P x3.

  Hint Unfold Directed : main.

  Theorem directed_complete :
    forall P,
    Directed P ->
    exists x, Supremum P x.
  Proof.
    search.
  Qed.

  #[local] Hint Resolve directed_complete : main.

  Definition bottom := tt.

  Hint Unfold bottom : main.

  Theorem bottom_least : forall x, Leq bottom x.
  Proof.
    search.
  Qed.

  #[local] Hint Resolve bottom_least : main.
End TrivialKleeneData.

Module TrivialKleeneDataTheorems := KleeneTheorems TrivialKleeneData.
