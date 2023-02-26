(******************************************************)
(******************************************************)
(****                                              ****)
(****   The simplest possible causal cover graph   ****)
(****                                              ****)
(******************************************************)
(******************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.CausalCoverGraph.CausalCoverGraph.
Require Import Main.Graphs.CausalCoverGraph.CausalCoverGraphTheorems.
Require Import Main.Tactics.

Module TrivialCausalCoverGraph <: CausalCoverGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition event := Empty_set.

  Definition causes (e1 e2 : event) := False.

  (* Coq requires that we copy this verbatim from `CausalCoverGraph`. *)
  Definition precedes := clos_refl_trans causes.

  #[export] Hint Unfold precedes : main.

  Definition cover (e1 e2 : event) := False.

  Theorem coverConvexity :
    forall e1 e2 e3,
    cover e1 e3 ->
    cover e2 e3 ->
    precedes e1 e2 ->
    e1 = e2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve coverConvexity : main.

  Theorem coverBoundedness : forall e1 e2, cover e1 e2 -> precedes e1 e2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve coverBoundedness : main.

  Theorem coverConnectedness :
    forall e1 e2 e3, causes e1 e2 -> precedes e2 e3 ->
    exists e4, cover e4 e3 /\ (precedes e4 e1 \/ precedes e2 e4).
  Proof.
    search.
  Qed.

  #[export] Hint Resolve coverConnectedness : main.
End TrivialCausalCoverGraph.

Module TrivialCausalCoverGraphTheorems :=
  CausalCoverGraphTheorems TrivialCausalCoverGraph.
