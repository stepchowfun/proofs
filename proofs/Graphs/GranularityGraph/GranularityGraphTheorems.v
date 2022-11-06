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
Require Import Main.Graphs.GranularityGraph.GranularityGraph.
Require Import Main.Tactics.

Module GranularityGraphTheorems (Graph : GranularityGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.

  (* The root only appears in the root grain. *)

  Theorem rootIncidenceLeft : forall g n, edge g root n -> g = root.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve rootIncidenceLeft : main.

  Theorem rootIncidenceRight : forall g n, edge g n root -> g = root.
  Proof.
    clean.
    pose proof (visibility g n root H).
    assert (visible g root); [eSearch | search].
  Qed.

  #[export] Hint Resolve rootIncidenceRight : main.

  (* The root is only reachable in the root grain. *)

  Theorem rootReachability :
    forall g n,
    n <> root ->
    reachable g n root ->
    g = root.
  Proof.
    clean.
    unfold reachable in H0.
    remember root in H0.
    induction H0; search.
    - rewrite Heqn0 in H0.
      apply rootIncidenceRight in H0.
      search.
    - destruct (classic (y = root)); search.
  Qed.

  #[export] Hint Resolve rootReachability : main.

  (* The root is only visible in the root grain. *)

  Theorem rootVisibility : forall g, visible g root -> g = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootVisibility : main.

  (* The only node that contains the root is itself. *)

  Theorem rootContainment : forall g, contains g root -> g = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootContainment : main.
End GranularityGraphTheorems.
