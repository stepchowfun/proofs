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
  Definition reachable g := clos_refl_trans (edge g).

  #[export] Hint Unfold reachable : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Definition visible g := reachable g g.

  #[export] Hint Unfold visible : main.

  Theorem visibility : forall g n1 n2, edge g n1 n2 -> visible g n1.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve visibility : main.

  (* Coq requires that we copy this verbatim from `GranularityGraph`. *)
  Definition contains := clos_refl_trans visible.

  #[export] Hint Unfold contains : main.

  Theorem reflection :
    forall g n1 n2 n3,
    visible g n1 ->
    visible g n2 ->
    contains n1 n3 ->
    contains n2 n3 ->
    edge g n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reflection : main.

  Theorem containment :
    forall n1 n2,
    contains n1 n2 ->
    contains n2 n1 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve containment : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootedness : forall n, contains root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootedness : main.
End TrivialGranularityGraph.

Module TrivialGranularityGraphTheorems :=
  GranularityGraphTheorems TrivialGranularityGraph.
