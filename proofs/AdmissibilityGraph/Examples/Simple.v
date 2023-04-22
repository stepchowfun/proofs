(******************************************)
(******************************************)
(****                                  ****)
(****   A simple admissibility graph   ****)
(****                                  ****)
(******************************************)
(******************************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.AdmissibilityGraph.AdmissibilityGraph.
Require Import Main.AdmissibilityGraph.AdmissibilityGraphTheorems.
Require Import Main.Tactics.

Module Simple <: AdmissibilityGraph.
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
    This admissibility graph corresponds to the picture located at:

      ../Images/graph-00.svg
  *)

  Inductive nodeLabels := A | B | C | D.

  #[export] Hint Constructors nodeLabels : main.

  Definition node : Type := nodeLabels.

  #[export] Hint Unfold node : main.

  Definition parent (n1 : node) (n2 : node) :=
    match n1, n2 with
    | A, A => True
    | B, A => True
    | C, A => True
    | D, A => False
    | A, B => False
    | B, B => True
    | C, B => False
    | D, B => False
    | A, C => False
    | B, C => False
    | C, C => True
    | D, C => True
    | A, D => False
    | B, D => False
    | C, D => False
    | D, D => True
    end.

  #[export] Hint Unfold parent : main.

  Theorem reflexivity : forall n, parent n n.
  Proof.
    clean.
    destruct n; search.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition admissible n1 n2 := exists n3, ancestor n1 n3 /\ parent n2 n3.

  #[export] Hint Unfold admissible : main.

  Definition dependency (n1 n2 : node) :=
    match n1, n2 with
    | A, A => True
    | A, B => True
    | A, C => True
    | A, D => False
    | B, A => True
    | B, B => True
    | B, C => True
    | B, D => False
    | C, A => True
    | C, B => True
    | C, C => True
    | C, D => True
    | D, A => True
    | D, B => True
    | D, C => True
    | D, D => True
    end.

  #[export] Hint Unfold dependency : main.

  Theorem admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.
  Proof.
    clean.
    destruct n1, n2; search; try (
      exists A + exists B + exists C + exists D;
      split; search; solve [
        apply t_trans with (y := A) +
        apply t_trans with (y := B) +
        apply t_trans with (y := C) +
        apply t_trans with (y := D);
        solve [search]
      ]
    ).
  Qed.

  #[export] Hint Resolve admissibility : main.
End Simple.

Module SimpleTheorems := AdmissibilityGraphTheorems Simple.
