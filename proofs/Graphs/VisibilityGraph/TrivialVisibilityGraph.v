(****************************************************)
(****************************************************)
(****                                            ****)
(****   The simplest possible visibility graph   ****)
(****                                            ****)
(****************************************************)
(****************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.VisibilityGraph.VisibilityGraph.
Require Import Main.Graphs.VisibilityGraph.VisibilityGraphTheorems.
Require Import Main.Tactics.

Module TrivialVisibilityGraph <: VisibilityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := Empty_set.

  Definition edge (n1 n2 : node) := False.

  Definition parent (p : node) (n : node) := False.

  (* Coq requires that we copy this verbatim from `VisibilityGraph`. *)
  Definition reachable := clos_refl_trans edge.

  #[export] Hint Unfold reachable : main.

  Theorem reachability : forall n1 n2, parent n1 n2 -> reachable n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reachability : main.

  Theorem visibility :
    forall n1 n2 n3, edge n1 n2 -> reachable n2 n3 ->
    exists n4, parent n4 n3 /\ (reachable n4 n1 \/ reachable n2 n4).
  Proof.
    search.
  Qed.

  #[export] Hint Resolve visibility : main.
End TrivialVisibilityGraph.

Module TrivialVisibilityGraphTheorems :=
  VisibilityGraphTheorems TrivialVisibilityGraph.
