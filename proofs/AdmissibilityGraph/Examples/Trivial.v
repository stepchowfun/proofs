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

  Definition node := Empty_set.

  #[export] Hint Unfold node : main.

  Definition dependency (n1 n2 : node) := False.

  #[export] Hint Unfold dependency : main.

  Definition parent (n1 : node) (n2 : node) := False.

  #[export] Hint Unfold parent : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition admissible n1 n2 :=
    exists n3 n4, ancestor n3 n1 /\ parent n3 n4 /\ ancestor n2 n4.

  #[export] Hint Unfold admissible : main.

  Theorem reflexivity : forall n, parent n n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  Theorem antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve antisymmetry : main.

  Theorem admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve admissibility : main.
End Trivial.

Module TrivialTheorems := AdmissibilityGraphTheorems Trivial.
