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

  #[local] Arguments clos_trans {A} _ _ _.
  #[local] Arguments clos_trans_1n {A} _ _ _.
  #[local] Arguments clos_trans_n1 {A} _ _ _.
  #[local] Hint Constructors clos_trans : main.
  #[local] Hint Constructors clos_trans_1n : main.
  #[local] Hint Constructors clos_trans_n1 : main.
  #[local] Hint Resolve clos_t1n_trans : main.
  #[local] Hint Resolve clos_trans_t1n : main.
  #[local] Hint Resolve clos_tn1_trans : main.
  #[local] Hint Resolve clos_trans_tn1 : main.

  (*
    If some target admits some source, any ancestor of that target admits that
    source.
  *)

  Theorem ancestorAdmissibility :
    forall n1 n2 n3, admissible n1 n2 -> ancestor n2 n3 -> admissible n1 n3.
  Proof.
    unfold admissible.
    clean.
    exists x, x0.
    repeat split; search.
    apply t_trans with (y := n2); search.
  Qed.

  #[export] Hint Resolve ancestorAdmissibility : main.

  (*
    If some target admits some source, that target admits any descendant of
    that source.
  *)

  Theorem descendantAdmissibility :
    forall n1 n2 n3, admissible n1 n2 -> ancestor n3 n1 -> admissible n3 n2.
  Proof.
    unfold admissible.
    clean.
    exists x, x0.
    repeat split; search.
    apply t_trans with (y := n1); search.
  Qed.

  #[export] Hint Resolve descendantAdmissibility : main.

  (* Nodes are admitted by themselves. *)

  Theorem selfAdmissibility : forall n, admissible n n.
  Proof.
    clean.
    unfold admissible.
    exists n, n.
    search.
  Qed.

  #[export] Hint Resolve selfAdmissibility : main.

  (* Nodes are admitted by ancestors of their children. *)

  Theorem ancestorOfChildAdmissibility :
    forall n1 n2 n3, parent n1 n2 -> ancestor n1 n3 -> admissible n2 n3.
  Proof.
    clean.
    unfold admissible.
    exists n2, n1.
    search.
  Qed.

  #[export] Hint Resolve ancestorOfChildAdmissibility : main.

  (* Nodes are admitted by children of their ancestors. *)

  Theorem childOfAncestorAdmissibility :
    forall n1 n2 n3, parent n1 n2 -> ancestor n3 n2 -> admissible n3 n1.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve childOfAncestorAdmissibility : main.
End AdmissibilityGraphTheorems.
