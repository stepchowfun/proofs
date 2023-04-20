(*******************************************************)
(*******************************************************)
(****                                               ****)
(****   The simplest possible admissibility graph   ****)
(****                                               ****)
(*******************************************************)
(*******************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.AdmissibilityGraph.AdmissibilityGraph.
Require Import Main.AdmissibilityGraph.AdmissibilityGraphTheorems.
Require Import Main.Tactics.

Module Trivial <: AdmissibilityGraph.
  #[local] Arguments clos_trans {A} _ _ _.
  #[local] Hint Constructors clos_trans : main.

  (* This admissibility graph has zero nodes or parent-child relationships. *)

  Definition node := Empty_set.

  #[export] Hint Unfold node : main.

  Definition parent (n1 : node) (n2 : node) := False.

  #[export] Hint Unfold parent : main.

  Theorem reflexivity : forall n, parent n n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition admissible n1 n2 :=
    exists n3 n4, ancestor n1 n3 /\ parent n4 n3 /\ ancestor n4 n2.

  #[export] Hint Unfold admissible : main.

  Definition dependency (n1 n2 : node) := False.

  #[export] Hint Unfold dependency : main.

  Theorem admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve admissibility : main.
End Trivial.

Module TrivialTheorems := AdmissibilityGraphTheorems Trivial.
