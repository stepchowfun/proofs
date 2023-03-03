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
Require Import Main.Graphs.Gigamesh.Gigamesh.
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
    *Reachability* is the reflexive transitive closure of the edge relation.
  *)

  Definition reachable := clos_refl_trans edge.

  #[export] Hint Unfold reachable : main.

  (* Parenthood implies reachability. *)

  Theorem parentReach :
    forall n1 n2, parent n1 n2 -> reachable n1 n2.
  Proof.
    clean.
    assert (
      clos_refl_trans_n1 (
        fun n2 n3 : node => edge n2 n3 /\ parent n1 n3
      ) n1 n2
    ); search.
    clear H.
    induction H0; eSearch.
  Qed.

  #[export] Hint Resolve parentReach : main.

  (* Ancestorship implies reachability. *)

  Theorem ancestorReach :
    forall n1 n2, ancestor n1 n2 -> reachable n1 n2.
  Proof.
    clean.
    induction H; eSearch.
  Qed.

  #[export] Hint Resolve ancestorReach : main.

  (* The root is the only node that can be a parent of the root. *)

  Theorem rootParent : forall n, parent n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootParent : main.

  (* The root is the only node that is an ancestor of the root. *)

  Theorem ancestorOfRoot : forall n, ancestor n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve ancestorOfRoot : main.
End GigameshTheorems.
