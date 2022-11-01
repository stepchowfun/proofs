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
    forall n1 n2,
    n2 <> root ->
    reachable n1 n2 root ->
    n1 = root.
  Proof.
    clean.
    unfold reachable in H0.
    remember root in H0.
    induction H0; search.
    - rewrite Heqn in H0.
      apply rootIncidenceRight in H0.
      search.
    - destruct (classic (y = root)); search.
  Qed.

  #[export] Hint Resolve rootReachability : main.

  (* The root is only visible in the root grain. *)

  Theorem rootVisibility : forall n, visible n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootVisibility : main.

  (* The only node that contains the root is itself. *)

  Theorem rootContainment : forall n, contains n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootContainment : main.

End GranularityGraphTheorems.
