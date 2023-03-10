(***************************************)
(***************************************)
(****                               ****)
(****   Theorems about gigameshes   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Main.Gigamesh.Gigamesh.
Require Import Main.Tactics.

Module GigameshTheorems (Graph : Gigamesh).
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
    If an edge is admitted, an edge from the source to any ancestor of the
    target is admitted as well.
  *)

  Theorem ancestorAdmission :
    forall n1 n2 n3, admitted n1 n2 -> ancestor n3 n2 -> admitted n1 n3.
  Proof.
    unfold admitted.
    clean.
    exists x.
    exists x0.
    repeat split; search.
    apply rt_trans with (y := n2); search.
  Qed.

  #[export] Hint Resolve ancestorAdmission : main.

  (*
    If an edge is admitted, an edge from a descendant of the source to the
    target is admitted as well.
  *)

  Theorem descendantAdmission :
    forall n1 n2 n3, admitted n1 n2 -> ancestor n1 n3 -> admitted n3 n2.
  Proof.
    unfold admitted.
    clean.
    exists x.
    exists x0.
    repeat split; search.
    apply rt_trans with (y := n1); search.
  Qed.

  #[export] Hint Resolve descendantAdmission : main.
End GigameshTheorems.
