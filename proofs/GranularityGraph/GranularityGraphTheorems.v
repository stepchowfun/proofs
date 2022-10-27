(***********************************************)
(***********************************************)
(****                                       ****)
(****   Theorems about granularity graphs   ****)
(****                                       ****)
(***********************************************)
(***********************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.GranularityGraph.GranularityGraph.
Require Import Main.Tactics.

Module GranularityGraphTheorems (Graph : GranularityGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.

  (*
    Each grain is reachable from all the objects in its associated subgraph.
  *)

  Theorem grainReachable : forall g n, visible g n -> reachable g n g.
  Proof.
    clean.
    apply sharing with (n3 := n); search.
  Qed.

  #[export] Hint Resolve grainReachable : main.

  (* The root only appears in the root grain. *)

  Theorem rootGranularityLeft : forall g n, edge g root n -> g = root.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve rootGranularityLeft : main.

  Theorem rootGranularityRight : forall g n, edge g n root -> g = root.
  Proof.
    clean.
    pose proof (visibility g n root H).
    assert (visible g root); [eSearch | search].
  Qed.

  #[export] Hint Resolve rootGranularityRight : main.

  (* The only node that contains the root is itself. *)

  Theorem rootUniquelyContained : forall n, contains n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootUniquelyContained : main.
End GranularityGraphTheorems.
