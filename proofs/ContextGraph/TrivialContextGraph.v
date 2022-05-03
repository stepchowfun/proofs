(*************************************************)
(*************************************************)
(****                                         ****)
(****   The simplest possible context graph   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Main.ContextGraph.Closure.
Require Import Main.ContextGraph.ContextGraph.
Require Import Main.Tactics.

Module TrivialContextGraph <: ContextGraph.
  Definition node := unit.

  Definition edge (x y z : node) := False.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition horizontallyReachable context := closure (edge context).

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition rooted context := horizontallyReachable context context.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition verticallyReachable := closure rooted.

  Theorem verticalAntisymmetry :
    forall node1 node2,
    verticallyReachable node1 node2 ->
    verticallyReachable node2 node1 ->
    node1 = node2.
  Proof.
    clean.
    elim node1.
    elim node2.
    magic.
  Qed.

  Theorem sourcesRooted :
    forall context source target,
    edge context source target ->
    rooted context source.
  Proof.
    magic.
  Qed.

  Definition origin := tt.

  Theorem originality : forall node, verticallyReachable origin node.
  Proof.
    clean.
    elim origin.
    elim node0.
    apply reflexivity.
  Qed.
End TrivialContextGraph.

Module TrivialContextGraphTheorems := ContextGraphTheorems TrivialContextGraph.
