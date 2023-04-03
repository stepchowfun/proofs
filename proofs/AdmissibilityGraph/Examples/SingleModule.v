(**************************************************************)
(**************************************************************)
(****                                                      ****)
(****   An admissibility graph which implements a module   ****)
(****                                                      ****)
(**************************************************************)
(**************************************************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.AdmissibilityGraph.AdmissibilityGraph.
Require Import Main.AdmissibilityGraph.AdmissibilityGraphTheorems.
Require Import Main.Tactics.

Module SingleModule <: AdmissibilityGraph.
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

      ../Images/graph-08.svg
  *)

  Inductive nodeLabels := Ingress | Egress | A | B | C.

  #[export] Hint Constructors nodeLabels : main.

  Definition node : Type := nodeLabels.

  #[export] Hint Unfold node : main.

  Definition parent (n1 : node) (n2 : node) :=
    match n1, n2 with
    | Ingress, Ingress => True
    | Egress , Ingress => False
    | A, Ingress => False
    | B, Ingress => False
    | C, Ingress => False
    | Ingress, Egress => False
    | Egress , Egress => True
    | A, Egress => True
    | B, Egress => True
    | C, Egress => True
    | Ingress, A => True
    | Egress , A => False
    | A, A => True
    | B, A => False
    | C, A => False
    | Ingress, B => True
    | Egress , B => False
    | A, B => False
    | B, B => True
    | C, B => False
    | Ingress, C => True
    | Egress , C => False
    | A, C => False
    | B, C => False
    | C, C => True
    end.

  #[export] Hint Unfold parent : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

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
    apply clos_trans_tn1 in H, H0.
    destruct n1, n2; solve [
      reflexivity + eliminate H + eliminate H0; solve [eliminate H1]
    ].
  Qed.

  #[export] Hint Resolve antisymmetry : main.

  (* Coq requires that we copy this verbatim from `AdmissibilityGraph`. *)
  Definition admissible n1 n2 :=
    exists n3 n4, ancestor n1 n3 /\ parent n4 n3 /\ ancestor n4 n2.

  #[export] Hint Unfold admissible : main.

  Definition dependency (n1 n2 : node) :=
    match n1, n2 with
    | Ingress, Ingress => True
    | Ingress, Egress => True
    | Ingress, A => True
    | Ingress, B => True
    | Ingress, C => True
    | Egress, Ingress => False
    | Egress, Egress => True
    | Egress, A => True
    | Egress, B => True
    | Egress, C => True
    | A, Ingress => True
    | A, Egress => True
    | A, A => True
    | A, B => True
    | A, C => True
    | B, Ingress => True
    | B, Egress => True
    | B, A => True
    | B, B => True
    | B, C => True
    | C, Ingress => True
    | C, Egress => True
    | C, A => True
    | C, B => True
    | C, C => True
    end.

  #[export] Hint Unfold dependency : main.

  Theorem admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.
  Proof.
    clean.
    unfold admissible.
    destruct n1, n2; search; try (
      exists Ingress + exists Egress + exists A + exists B + exists C;
      exists Ingress + exists Egress + exists A + exists B + exists C;
      split; search; solve [
        apply t_trans with (y := Ingress) +
        apply t_trans with (y := Egress) +
        apply t_trans with (y := A) +
        apply t_trans with (y := B) +
        apply t_trans with (y := C);
        solve [search]
      ]
    ).
  Qed.

  #[export] Hint Resolve admissibility : main.
End SingleModule.

Module ModuleTheorems := AdmissibilityGraphTheorems SingleModule.
