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

  (* Every node in a grain has a loop in that grain. *)

  Theorem reflexivity : forall g n, contains g n -> edge g n n.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  (* The root only appears in the root grain. *)

  Theorem rootGranularityLeft : forall g n, edge g root n -> g = root.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve rootGranularityLeft : main.

  Theorem rootGranularityRight : forall g n, edge g n root -> g = root.
  Proof.
    clean.
    pose proof (containment g n root H).
    assert (contains g root); [eSearch | search].
  Qed.

  #[export] Hint Resolve rootGranularityRight : main.

  (* The only node that can vertically reach the root is itself. *)

  Theorem rootUniquelyReachable :
    forall n,
    verticallyReachable n root ->
    n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootUniquelyReachable : main.
End GranularityGraphTheorems.
