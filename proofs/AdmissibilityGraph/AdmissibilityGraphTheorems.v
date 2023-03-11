(*************************************************)
(*************************************************)
(****                                         ****)
(****   Theorems about admissibility graphs   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.AdmissibilityGraph.AdmissibilityGraph.
Require Import Main.Tactics.

Module AdmissibilityGraphTheorems (Graph : AdmissibilityGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Arguments clos_refl_trans_1n {A} _ _ _.
  #[local] Arguments clos_refl_trans_n1 {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.
  #[local] Hint Constructors clos_refl_trans_1n : main.
  #[local] Hint Constructors clos_refl_trans_n1 : main.
  #[local] Hint Resolve clos_rt1n_rt : main.
  #[local] Hint Resolve clos_rt_rt1n : main.
  #[local] Hint Resolve clos_rtn1_rt : main.
  #[local] Hint Resolve clos_rt_rtn1 : main.

  (*
    If some source can reference some target, that source can reference any
    ancestor of that target as well.
  *)

  Theorem ancestorAdmissibility :
    forall n1 n2 n3, admissible n1 n2 -> ancestor n3 n2 -> admissible n1 n3.
  Proof.
    unfold admissible.
    clean.
    exists x, x0.
    repeat split; search.
    apply rt_trans with (y := n2); search.
  Qed.

  #[export] Hint Resolve ancestorAdmissibility : main.

  (*
    If some source can reference some target, any descendant of that source can
    reference that target as well.
  *)

  Theorem descendantAdmissibility :
    forall n1 n2 n3, admissible n1 n2 -> ancestor n1 n3 -> admissible n3 n2.
  Proof.
    unfold admissible.
    clean.
    exists x, x0.
    repeat split; search.
    apply rt_trans with (y := n1); search.
  Qed.

  #[export] Hint Resolve descendantAdmissibility : main.
End AdmissibilityGraphTheorems.
