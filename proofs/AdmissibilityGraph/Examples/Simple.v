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

  Inductive nodeLabels := A | B | C | D.

  #[export] Hint Constructors nodeLabels : main.

  Definition node : Type := nodeLabels.

  #[export] Hint Unfold node : main.

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

  Definition parent (n1 : node) (n2 : node) :=
    match n1, n2 with
    | A, A => True
    | A, B => True
    | A, C => True
    | A, D => False
    | B, A => False
    | B, B => True
    | B, C => False
    | B, D => False
    | C, A => False
    | C, B => False
    | C, C => True
    | C, D => True
    | D, A => False
    | D, B => False
    | D, C => False
    | D, D => True
    end.

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
    clean.
    destruct n; search.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  Theorem antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    #[local] Ltac eliminate H :=
      match type of H with
      | clos_trans_n1 parent ?n1 ?n2 =>
        remember n2; induction H; repeat match goal with
        | [n : node |- _] => destruct n; search
        end
      end.

    clean.
    apply clos_trans_tn1 in H.
    apply clos_trans_tn1 in H0.
    destruct n1, n2; search;
      try solve [eliminate H; eliminate H1];
      try solve [eliminate H0; eliminate H1].
  Qed.

  #[export] Hint Resolve antisymmetry : main.

  Theorem admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.
  Proof.
    clean.
    unfold admissible.
    destruct n1, n2; search; try (
      exists A + exists B + exists C + exists D;
      exists A + exists B + exists C + exists D;
      solve [search]
    ).
    exists A, B.
    split; search.
    apply t_trans with (y := C); search.
  Qed.

  #[export] Hint Resolve admissibility : main.
End Simple.

Module SimpleTheorems := AdmissibilityGraphTheorems Simple.
