(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   The simplest possible granularity graph   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.GranularityGraph.GranularityGraph.
Require Import Main.GranularityGraph.GranularityGraphTheorems.
Require Import Main.Tactics.

Module TrivialGranularityGraph <: GranularityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (g n1 n2 : node) := True.

  #[export] Hint Unfold edge : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Definition horizontallyReachable g := clos_refl_trans (edge g).

  #[export] Hint Unfold horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Definition contains g := horizontallyReachable g g.

  #[export] Hint Unfold contains : main.

  Theorem containment : forall g n1 n2, edge g n1 n2 -> contains g n1.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve containment : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Definition verticallyReachable := clos_refl_trans contains.

  #[export] Hint Unfold verticallyReachable : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Theorem reflection :
    forall g n1 n2 n3,
    contains g n1 ->
    contains g n2 ->
    verticallyReachable n1 n3 ->
    verticallyReachable n2 n3 ->
    edge g n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reflection : main.

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve verticalAntisymmetry : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootReach : main.
End TrivialGranularityGraph.

Module TrivialGranularityGraphTheorems :=
  GranularityGraphTheorems TrivialGranularityGraph.
