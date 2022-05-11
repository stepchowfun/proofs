(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   The simplest possible pointed directed-complete partial order   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

Require Import Main.Kleene.Kleene.
Require Import Main.Tactics.

Module TrivialKleeneData <: KleeneData.
  Definition T := unit.

  Definition leq (x y : T) := True.

  Theorem reflexivity : forall x, leq x x.
  Proof.
    unfold leq.
    magic.
  Qed.

  #[local] Hint Resolve reflexivity : main.

  Theorem transitivity : forall x y z, leq x y -> leq y z -> leq x z.
  Proof.
    unfold leq.
    magic.
  Qed.

  #[local] Hint Resolve transitivity : main.

  Theorem antisymmetry : forall x y, leq x y -> leq y x -> x = y.
  Proof.
    clean.
    destruct x.
    destruct y.
    magic.
  Qed.

  #[local] Hint Resolve antisymmetry : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition supremum P x1 :=
    (forall x2, P x2 -> leq x2 x1) /\
    forall x3, (forall x2, P x2 -> leq x2 x3) -> leq x1 x3.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition directed P :=
    (exists x1, P x1) /\
    forall x1 x2, P x1 -> P x2 -> exists x3, leq x1 x3 /\ leq x2 x3 /\ P x3.

  Theorem directedComplete :
    forall P,
    directed P ->
    exists x, supremum P x.
  Proof.
    clean.
    exists tt.
    split; unfold leq; magic.
  Qed.

  #[local] Hint Resolve directedComplete : main.

  Definition bottom := tt.

  Theorem bottomLeast : forall x, leq bottom x.
  Proof.
    unfold leq.
    magic.
  Qed.

  #[local] Hint Resolve bottomLeast : main.
End TrivialKleeneData.

Module TrivialKleeneDataTheorems := KleeneTheorems TrivialKleeneData.
