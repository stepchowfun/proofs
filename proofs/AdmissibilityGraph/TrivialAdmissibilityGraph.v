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

Module TrivialAdmissibilityGraph <: AdmissibilityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := Empty_set.

  #[export] Hint Unfold node : main.

  Definition reference (n1 n2 : node) := False.

  #[export] Hint Unfold reference : main.

  Definition parent (n1 : node) (n2 : node) := False.

  #[export] Hint Unfold parent : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition ancestor := clos_refl_trans parent.

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

  Theorem admissibility : forall n1 n2, reference n1 n2 -> admissible n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve admissibility : main.
End TrivialAdmissibilityGraph.

Module TrivialAdmissibilityGraphTheorems :=
  AdmissibilityGraphTheorems TrivialAdmissibilityGraph.
